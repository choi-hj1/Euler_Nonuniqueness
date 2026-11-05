import EulerNonuniqueness.Section3.MovingCentroidGaugeMaterial
import EulerNonuniqueness.Section3.MovingMaterialInitialDisks

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

theorem clock_initial
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial) :
    trajectory.clock 0 = initial.1 := by
  rw [clock, EulerNonuniqueness.General.odePrimitiveExtension_initial, trajectory.initial_identity]

theorem center_initial
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial) (index : Fin count) :
    trajectory.center index 0 = initial.2.1 index := by
  rw [center, EulerNonuniqueness.General.odePrimitiveExtension_initial, trajectory.initial_identity]

theorem movingPatch_shape_initial
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial) (index : Fin count) :
    (trajectory.movingPatch index).shape 0 = initial.2.2 index :=
  congrArg (fun state : MovingContourState count => state.2.2 index) trajectory.initial_identity

theorem movingPatch_phase_initial
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialClock : initial.1 = 0) (index : Fin count) : (trajectory.movingPatch index).phase 0 = 0 := by
  change (configuration.density index / 2) * trajectory.clock 0 = 0
  rw [trajectory.clock_initial, initialClock, mul_zero]

theorem movingPatch_domain_initial_circle
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach) (index : Fin count) :
    (trajectory.movingPatch index).domain 0 = Metric.ball (initial.2.1 index) (configuration.radius index) := by
  have circle : (trajectory.movingPatch index).shape 0 = standardCircleBanach :=
    (trajectory.movingPatch_shape_initial index).trans (initialCircles index)
  rw [(trajectory.movingPatch index).domain_eq_ball_of_circle circle]
  change Metric.ball (trajectory.center index 0) (configuration.radius index) = _
  rw [trajectory.center_initial]

theorem movingPatch_area_initial_circle
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach) (index : Fin count) :
    volume.real ((trajectory.movingPatch index).domain 0) = Real.pi * (configuration.radius index) ^ 2 :=
  (trajectory.movingPatch index).domain_area_at_circle
    ((trajectory.movingPatch_shape_initial index).trans (initialCircles index))

theorem clock_eq_time_of_margin
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialClock : initial.1 = 0) (marginPositive : 0 < margin) {horizon time : ℝ}
    (inside : time ∈ Icc 0 horizon)
    (safe : ∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) : trajectory.clock time = time := by
  rw [clock, EulerNonuniqueness.General.odePrimitiveExtension, trajectory.initial_identity, initialClock, zero_add]
  calc
    _ = ∫ current in (0 : ℝ)..time, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro current member
      change (trajectory.velocity current).1 = 1
      rw [uIcc_of_le inside.1] at member
      rw [trajectory.velocity_eq_uncut_of_margin marginPositive current (safe current ⟨member.1, member.2.trans inside.2⟩)]
      rfl
    _ = time := by simp

theorem movingPatch_phase_eq_density_time_of_margin
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialClock : initial.1 = 0) (marginPositive : 0 < margin) {horizon time : ℝ}
    (inside : time ∈ Icc 0 horizon)
    (safe : ∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) (index : Fin count) :
    (trajectory.movingPatch index).phase time = configuration.density index * time / 2 := by
  change (configuration.density index / 2) * trajectory.clock time = _
  rw [trajectory.clock_eq_time_of_margin initialClock marginPositive inside safe]
  ring

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
