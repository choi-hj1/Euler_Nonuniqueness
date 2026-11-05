import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_operator_comp_difference_le
    (firstOuter finalOuter firstInner finalInner : Space →L[ℝ] Space) :
    ‖firstOuter.comp firstInner - finalOuter.comp finalInner‖ ≤
      ‖firstOuter‖ * ‖firstInner - finalInner‖ + ‖firstOuter - finalOuter‖ * ‖finalInner‖ := by
  have identity : firstOuter.comp firstInner - finalOuter.comp finalInner =
      firstOuter.comp (firstInner - finalInner) + (firstOuter - finalOuter).comp finalInner := by
    ext direction
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [identity]
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _))

end EulerNonuniqueness.General
