import EulerNonuniqueness.Section3.CanonicalExteriorContourForcing
import EulerNonuniqueness.Section3.MovingCentroidGaugeInitialData
import EulerNonuniqueness.Section6.MovingGaugeExternalForcing

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

theorem movingStatePhase_eq_density_time_of_margin
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialClock : initial.1 = 0) (marginPositive : 0 < margin) {horizon time : ℝ}
    (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (nonnegativeTime : time ∈ Icc 0 horizon)
    (safe : ∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) (index : Fin count) :
    configuration.movingStatePhase (trajectory.curve time) index = Circle.exp (configuration.density index * time / 2) := by
  change Circle.exp ((configuration.density index / 2) * (trajectory.curve time).1) = _
  rw [← trajectory.clock_eq_curve inside,
    trajectory.clock_eq_time_of_margin initialClock marginPositive nonnegativeTime safe]
  congr 1
  ring

theorem movingStateExternalField_eq_canonical_of_margin
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialClock : initial.1 = 0) (marginPositive : 0 < margin) {horizon time distance : ℝ}
    (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (nonnegativeTime : time ∈ Icc 0 horizon)
    (safe : ∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) (index : Fin count)
    (positive : 0 < distance) (small : 8 * (trajectory.movingFamily.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (trajectory.movingFamily.patch source).domain time,
      distance ≤ ‖(trajectory.movingFamily.patch index).center time - position‖) :
    configuration.movingStateExternalField (trajectory.curve time) index =
      trajectory.movingFamily.canonicalExteriorContourForcing index time distance positive small separated
        ((trajectory.curve time).2.2 index)
        (configuration.movingStateAdmissible_shapes_bounded
          ((trajectory.shape_small.trans_le (min_le_left _ _)).le.trans (by norm_num)) (trajectory.admissible time) index)
        (Circle.exp (configuration.density index * time / 2)) := by
  have fieldIdentity : trajectory.externalSourceField time index =
      biotSavart (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) time) :=
    trajectory.movingFamily.finiteDomainSourceField_eq_biotSavart (Finset.univ.erase index) time
  have phaseIdentity := trajectory.movingStatePhase_eq_density_time_of_margin initialClock marginPositive
    inside nonnegativeTime safe index
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [trajectory.movingStateExternalField_value inside index label,
    FiniteMovingPatchFamily.canonicalExteriorContourForcing_value]
  rw [← fieldIdentity]
  change (configuration.radius index)⁻¹ •
      (((configuration.movingStatePhase (trajectory.curve time) index : ℂ)⁻¹) *
        trajectory.externalSourceField time index
          ((trajectory.curve time).2.1 index + configuration.radius index •
            ((configuration.movingStatePhase (trajectory.curve time) index : ℂ) *
              ((trajectory.curve time).2.2 index).val.1 label))) =
    (configuration.radius index)⁻¹ •
      (((Circle.exp (configuration.density index * time / 2) : Circle) : ℂ)⁻¹ *
        trajectory.externalSourceField time index
          (trajectory.center index time + configuration.radius index •
            ((Circle.exp (configuration.density index * time / 2) : ℂ) *
              ((trajectory.curve time).2.2 index).val.1 label)))
  rw [trajectory.center_eq_curve inside index, phaseIdentity]

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
