import EulerNonuniqueness.General.QuotientDifferenceBound
import Mathlib.Analysis.Complex.Basic

noncomputable section

namespace EulerNonuniqueness.Section6

theorem positiveLogForcing_relative_bound (firstPositive secondPositive : ℂ) (firstForce secondForce : ℂ × ℂ)
    {length positions : ℝ} (lengthPositive : 0 < length) (positionsNonnegative : 0 ≤ positions)
    (firstLower : length / 2 ≤ ‖firstPositive‖) (secondLower : length / 2 ≤ ‖secondPositive‖)
    (differenceBound : ‖firstPositive - secondPositive‖ ≤ length * positions) :
    ‖firstForce.1 / firstPositive - secondForce.1 / secondPositive‖ ≤
      2 * (‖firstForce - secondForce‖ / length) + 4 * (‖firstForce‖ / length) * positions := by
  have actual := EulerNonuniqueness.General.norm_quotient_difference_le secondForce.1 firstForce.1
    secondPositive firstPositive (by positivity : 0 < length / 2) secondLower firstLower
  rw [norm_sub_rev (secondForce.1 / secondPositive), norm_sub_rev secondForce.1,
    norm_sub_rev secondPositive] at actual
  have enlarged := actual.trans (add_le_add
    (div_le_div_of_nonneg_right (norm_fst_le (firstForce - secondForce)) (by positivity))
    (div_le_div_of_nonneg_right
      (mul_le_mul (norm_fst_le firstForce) differenceBound (norm_nonneg _) (norm_nonneg _)) (by positivity)))
  exact enlarged.trans_eq (by field_simp [lengthPositive.ne']; ring)

end EulerNonuniqueness.Section6
