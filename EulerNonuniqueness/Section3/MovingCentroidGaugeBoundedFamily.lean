import EulerNonuniqueness.Section3.MovingCentroidGaugeJointFamily
import EulerNonuniqueness.General.TrajectoryMargin

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingGaugeBoundedHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingGaugeBoundedC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem FiniteContourConfiguration.exists_bounded_joint_movingCentroidGaugeTrajectories {count : ℕ}
    (configuration : FiniteContourConfiguration count) :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ centerBound ≥ 0, ∀ gap > 0, ∀ margin > 0, ∀ backwardHorizon > 0, ∀ forwardHorizon > 0,
      ∃ bound : NNReal,
      ∃ trajectories : (initial : configuration.movingStateAdmissible centerBound shapeRadius gap) →
        MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial.val,
        Continuous (fun point : configuration.movingStateAdmissible centerBound shapeRadius gap × ℝ =>
          (trajectories point.1).curve point.2) ∧
        ∀ initial time, ‖(trajectories initial).velocity time‖ ≤ bound := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, uniformBounds⟩ :=
    configuration.exists_movingStateVectorField_uniform_bounds
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro centerBound centerNonnegative gap gapPositive margin marginPositive backwardHorizon backwardPositive forwardHorizon forwardPositive
  obtain ⟨fieldConstant, bound, fieldLipschitz, fieldBound⟩ :=
    uniformBounds centerBound centerNonnegative gap gapPositive
  have lipschitz := EulerNonuniqueness.General.lipschitzWith_distanceFieldCutoff_smul
    configuration.movingStateVectorField (configuration.movingStateAdmissible centerBound shapeRadius gap)
    marginPositive fieldConstant bound fieldLipschitz fieldBound
  have bounded := EulerNonuniqueness.General.distanceFieldCutoff_smul_norm_bound
    configuration.movingStateVectorField (configuration.movingStateAdmissible centerBound shapeRadius gap)
    marginPositive bound fieldBound
  obtain ⟨flow, initialIdentity, jointContinuous, equation, clamped⟩ :=
    exists_jointly_continuous_clamped_two_sided_family_of_bounded_lipschitz_ODE
      lipschitz bounded backwardPositive forwardPositive
  have admissible : ∀ initial ∈ configuration.movingStateAdmissible centerBound shapeRadius gap,
      ∀ time, flow initial time ∈ configuration.movingStateAdmissible centerBound shapeRadius gap := by
    intro initial initialInside
    have curveContinuous : Continuous (flow initial) := jointContinuous.comp (continuous_const.prodMk continuous_id)
    have initialMember : flow initial 0 ∈ configuration.movingStateAdmissible centerBound shapeRadius gap := by
      rw [initialIdentity]
      exact initialInside
    have fieldZero : ∀ state ∉ configuration.movingStateAdmissible centerBound shapeRadius gap,
        configuration.movingStateCutoffField centerBound shapeRadius gap margin state = 0 := by
      intro state outside
      unfold FiniteContourConfiguration.movingStateCutoffField
      rw [EulerNonuniqueness.General.distanceFieldCutoff_zero_outside _ margin state outside, zero_smul]
    exact EulerNonuniqueness.General.two_sided_trajectory_mem_of_lipschitz_field_zero_outside
      (trajectory := flow initial) lipschitz (configuration.movingStateAdmissible centerBound shapeRadius gap)
      fieldZero backwardPositive forwardPositive curveContinuous (equation initial) initialMember (clamped initial)
  let trajectories : (initial : configuration.movingStateAdmissible centerBound shapeRadius gap) →
      MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial.val :=
    fun initial => {
      backward_positive := backwardPositive
      forward_positive := forwardPositive
      shape_small := shapeSmall
      gap_positive := gapPositive
      curve := flow initial.val
      velocity := fun time => configuration.movingStateCutoffField centerBound shapeRadius gap margin (flow initial.val time)
      initial_identity := initialIdentity initial.val
      continuous := jointContinuous.comp (continuous_const.prodMk continuous_id)
      velocity_identity := fun _ => rfl
      velocity_continuous := lipschitz.continuous.comp (jointContinuous.comp (continuous_const.prodMk continuous_id))
      admissible := admissible initial.val initial.property
      equation := equation initial.val }
  refine ⟨bound, trajectories,
    jointContinuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd), ?_⟩
  intro initial time
  exact bounded (flow initial.val time)

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

theorem displacement_le_of_velocity_bound
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {bound time : ℝ} (bounded : ∀ current ∈ Ioo (-backwardHorizon) forwardHorizon, ‖trajectory.velocity current‖ ≤ bound)
    (nonnegative : 0 ≤ time) (beforeFinal : time < forwardHorizon) :
    ‖trajectory.curve time - initial‖ ≤ bound * time := by
  have movement := EulerNonuniqueness.General.trajectory_displacement_le_of_hasDerivAt_bound
    (Space := MovingContourState count) (curve := trajectory.curve) (velocity := trajectory.velocity)
    trajectory.backward_positive trajectory.equation bounded nonnegative beforeFinal
  simpa only [trajectory.initial_identity] using movement

theorem margin_of_velocity_bound
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {bound horizon : ℝ} (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ current ∈ Ioo (-backwardHorizon) forwardHorizon, ‖trajectory.velocity current‖ ≤ bound)
    (beforeFinal : horizon < forwardHorizon)
    (initialMargin : margin + bound * horizon ≤ infDist initial
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) :
    ∀ time ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve time)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ := by
  intro time inside
  apply EulerNonuniqueness.General.infDist_lower_bound_of_displacement _ initialMargin
  rw [dist_eq_norm (trajectory.curve time) initial]
  exact (trajectory.displacement_le_of_velocity_bound bounded inside.1 (inside.2.trans_lt beforeFinal)).trans
    (mul_le_mul_of_nonneg_left inside.2 boundNonnegative)

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
