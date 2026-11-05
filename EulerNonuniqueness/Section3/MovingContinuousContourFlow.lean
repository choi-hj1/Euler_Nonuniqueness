import EulerNonuniqueness.Section3.MovingContinuousContourField

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingContinuousFlowHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingContinuousFlowC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem FiniteContourConfiguration.exists_jointly_continuous_moving_cutoff_flow_in_continuous_submodule {count : ℕ}
    (configuration : FiniteContourConfiguration count) :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ centerBound ≥ 0, ∀ gap > 0, ∀ margin > 0, ∀ horizon ≥ 0,
      ∃ flow : MovingContourState count → ℝ → MovingContourState count,
        (∀ initial, flow initial 0 = initial) ∧
        Continuous (fun point : MovingContourState count × ℝ => flow point.1 point.2) ∧
        (∀ initial time, time ∈ Icc 0 horizon → HasDerivWithinAt (flow initial)
          (configuration.movingStateCutoffField centerBound shapeRadius gap margin (flow initial time))
          (Icc 0 horizon) time) ∧
        ∀ initial ∈ movingContinuousContourSubmodule count, ∀ time ∈ Icc 0 horizon,
          flow initial time ∈ movingContinuousContourSubmodule count := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, bounds⟩ := configuration.exists_movingStateVectorField_uniform_bounds
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro centerBound centerNonnegative gap gapPositive margin marginPositive horizon horizonNonnegative
  obtain ⟨fieldConstant, bound, lipschitz, bounded⟩ := bounds centerBound centerNonnegative gap gapPositive
  have cutoffLipschitz := EulerNonuniqueness.General.lipschitzWith_distanceFieldCutoff_smul
    configuration.movingStateVectorField (configuration.movingStateAdmissible centerBound shapeRadius gap)
    marginPositive fieldConstant bound lipschitz bounded
  have cutoffBound := EulerNonuniqueness.General.distanceFieldCutoff_smul_norm_bound
    configuration.movingStateVectorField (configuration.movingStateAdmissible centerBound shapeRadius gap)
    marginPositive bound bounded
  obtain ⟨flow, initialIdentity, jointContinuous, equation, _stability⟩ :=
    exists_jointly_continuous_family_of_bounded_lipschitz_ODE_with_closed_derivatives
      cutoffLipschitz cutoffBound horizonNonnegative
  refine ⟨flow, initialIdentity, jointContinuous, equation, ?_⟩
  intro initial initialMember
  have banachSmall : shapeRadius < min 1 (2 / (3 * Real.pi)) :=
    lt_min ((shapeSmall.trans_le (min_le_left _ _)).trans (by norm_num))
      (shapeSmall.trans_le (min_le_right _ _))
  apply EulerNonuniqueness.General.trajectory_mem_closed_submodule_of_bounded_lipschitz_field
    (movingContinuousContourSubmodule count) (movingContinuousContourSubmodule_closed count)
    cutoffLipschitz cutoffBound
    (configuration.movingStateCutoffField_mem_continuousSubmodule banachSmall)
    horizonNonnegative (jointContinuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    (equation initial)
  change flow initial 0 ∈ movingContinuousContourSubmodule count
  rw [initialIdentity]
  exact initialMember

end EulerNonuniqueness.Paper
