import Mathlib.Analysis.Normed.Group.Basic

namespace EulerNonuniqueness.General

variable {Space : Type*} [SeminormedAddCommGroup Space]

theorem norm_residual_difference_le_of_linear_taylor
    (first final firstLinear finalLinear firstTaylor finalTaylor : Space)
    (firstIdentity : first - firstLinear = firstTaylor)
    (finalIdentity : final - finalLinear = finalTaylor) :
    ‖first - final‖ ≤ ‖firstLinear - finalLinear‖ + ‖firstTaylor - finalTaylor‖ := by
  have firstValue := sub_eq_iff_eq_add.mp firstIdentity
  have finalValue := sub_eq_iff_eq_add.mp finalIdentity
  have equality : first - final = (firstLinear - finalLinear) + (firstTaylor - finalTaylor) := by
    rw [firstValue, finalValue]
    abel
  rw [equality]
  exact norm_add_le _ _

end EulerNonuniqueness.General
