import EulerNonuniqueness.Section3.UniformMovingCentroidGaugeRadius
import EulerNonuniqueness.Section3.MovingCentroidGaugeJointFamily
import EulerNonuniqueness.Section3.MovingContinuousContourField

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance uniformContinuousGaugeHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance uniformContinuousGaugeC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem exists_uniform_moving_continuous_gauge_trajectory_families :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ count : ℕ, ∀ configuration : FiniteContourConfiguration count,
      ∀ centerBound ≥ 0, ∀ gap > 0, ∀ margin > 0, ∀ backwardHorizon > 0, ∀ forwardHorizon > 0,
      ∃ trajectories : (initial : configuration.movingStateAdmissible centerBound shapeRadius gap) →
        MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
          backwardHorizon forwardHorizon initial.val,
        Continuous (fun point : configuration.movingStateAdmissible centerBound shapeRadius gap × ℝ =>
          (trajectories point.1).curve point.2) ∧
        ∀ initial, initial.val ∈ movingContinuousContourSubmodule count →
          ∀ time ∈ Ico 0 forwardHorizon,
            (trajectories initial).curve time ∈ movingContinuousContourSubmodule count := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, uniformBounds⟩ :=
    exists_uniform_moving_centroid_gauge_shape_radius
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro count configuration centerBound centerNonnegative gap gapPositive margin marginPositive
    backwardHorizon backwardPositive forwardHorizon forwardPositive
  obtain ⟨fieldConstant, bound, fieldLipschitz, fieldBound⟩ :=
    uniformBounds count configuration centerBound centerNonnegative gap gapPositive
  have lipschitz := EulerNonuniqueness.General.lipschitzWith_distanceFieldCutoff_smul
    configuration.movingStateVectorField (configuration.movingStateAdmissible centerBound shapeRadius gap)
    marginPositive fieldConstant bound fieldLipschitz fieldBound
  have bounded := EulerNonuniqueness.General.distanceFieldCutoff_smul_norm_bound
    configuration.movingStateVectorField (configuration.movingStateAdmissible centerBound shapeRadius gap)
    marginPositive bound fieldBound
  obtain ⟨flow, initialIdentity, jointContinuous, equation, clamped⟩ :=
    exists_jointly_continuous_clamped_two_sided_family_of_bounded_lipschitz_ODE
      lipschitz bounded backwardPositive forwardPositive
  have admissible : ∀ initial ∈ configuration.movingStateAdmissible centerBound shapeRadius gap, ∀ time,
      flow initial time ∈ configuration.movingStateAdmissible centerBound shapeRadius gap := by
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
      MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
        backwardHorizon forwardHorizon initial.val := fun initial => {
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
  refine ⟨trajectories, ?_, ?_⟩
  · exact jointContinuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  · intro initial initialMember time inside
    have banachSmall : shapeRadius < min 1 (2 / (3 * Real.pi)) :=
      lt_min ((shapeSmall.trans_le (min_le_left _ _)).trans (by norm_num))
        (shapeSmall.trans_le (min_le_right _ _))
    have invariant := EulerNonuniqueness.General.trajectory_mem_closed_submodule_of_bounded_lipschitz_field
      (movingContinuousContourSubmodule count) (movingContinuousContourSubmodule_closed count)
      lipschitz bounded (configuration.movingStateCutoffField_mem_continuousSubmodule banachSmall)
      inside.1 (jointContinuous.comp (continuous_const.prodMk continuous_id)).continuousOn
      (fun current currentInside => (equation initial.val current
        ⟨(neg_neg_of_pos backwardPositive).trans_le currentInside.1,
          currentInside.2.trans_lt inside.2⟩).hasDerivWithinAt)
      (by
        change flow initial.val 0 ∈ movingContinuousContourSubmodule count
        rw [initialIdentity]
        exact initialMember)
    exact invariant time ⟨inside.1, le_rfl⟩

end EulerNonuniqueness.Paper
