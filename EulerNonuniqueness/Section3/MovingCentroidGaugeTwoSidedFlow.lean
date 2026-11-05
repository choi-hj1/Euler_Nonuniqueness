import EulerNonuniqueness.Section3.MovingCentroidGaugeExistence
import EulerNonuniqueness.General.TwoSidedODEFamily
import EulerNonuniqueness.General.TwoSidedODEInvariance

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingGaugeTwoSidedHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingGaugeTwoSidedC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def FiniteContourConfiguration.movingStateCutoffField {count : ℕ}
    (configuration : FiniteContourConfiguration count) (centerBound shapeRadius gap margin : ℝ)
    (state : MovingContourState count) : MovingContourState count :=
  EulerNonuniqueness.General.distanceFieldCutoff
    (configuration.movingStateAdmissible centerBound shapeRadius gap) margin state •
      configuration.movingStateVectorField state

theorem FiniteContourConfiguration.exists_two_sided_moving_centroid_gauge_cutoff_family {count : ℕ}
    (configuration : FiniteContourConfiguration count) :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ centerBound ≥ 0, ∀ gap > 0, ∀ margin > 0, ∀ backwardHorizon > 0, ∀ forwardHorizon > 0,
      ∃ flow : MovingContourState count → ℝ → MovingContourState count,
        Continuous (configuration.movingStateCutoffField centerBound shapeRadius gap margin) ∧
        (∀ initial, flow initial 0 = initial) ∧
        Continuous (fun point : MovingContourState count × ℝ => flow point.1 point.2) ∧
        (∀ initial time, time ∈ Ioo (-backwardHorizon) forwardHorizon → HasDerivAt (flow initial)
          (configuration.movingStateCutoffField centerBound shapeRadius gap margin (flow initial time)) time) ∧
        ∀ initial ∈ configuration.movingStateAdmissible centerBound shapeRadius gap, ∀ time,
          flow initial time ∈ configuration.movingStateAdmissible centerBound shapeRadius gap := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, uniformBounds⟩ := configuration.exists_movingStateVectorField_uniform_bounds
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro centerBound centerNonnegative gap gapPositive margin marginPositive backwardHorizon backwardPositive forwardHorizon forwardPositive
  obtain ⟨fieldConstant, bound, fieldLipschitz, fieldBound⟩ := uniformBounds centerBound centerNonnegative gap gapPositive
  have lipschitz := EulerNonuniqueness.General.lipschitzWith_distanceFieldCutoff_smul
    configuration.movingStateVectorField (configuration.movingStateAdmissible centerBound shapeRadius gap)
    marginPositive fieldConstant bound fieldLipschitz fieldBound
  have bounded := EulerNonuniqueness.General.distanceFieldCutoff_smul_norm_bound
    configuration.movingStateVectorField (configuration.movingStateAdmissible centerBound shapeRadius gap)
    marginPositive bound fieldBound
  obtain ⟨flow, initialIdentity, jointContinuous, equation, clamped⟩ :=
    exists_jointly_continuous_clamped_two_sided_family_of_bounded_lipschitz_ODE lipschitz bounded backwardPositive forwardPositive
  refine ⟨flow, lipschitz.continuous, initialIdentity, jointContinuous, equation, ?_⟩
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

end EulerNonuniqueness.Paper
