import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace EulerNonuniqueness.General

theorem norm_quotient_difference_le {Value : Type*} [NormedField Value]
    (firstNumerator secondNumerator firstDenominator secondDenominator : Value)
    {gap : ℝ} (gapPositive : 0 < gap)
    (firstSeparated : gap ≤ ‖firstDenominator‖) (secondSeparated : gap ≤ ‖secondDenominator‖) :
    ‖firstNumerator / firstDenominator - secondNumerator / secondDenominator‖ ≤
      ‖firstNumerator - secondNumerator‖ / gap +
        ‖secondNumerator‖ * ‖firstDenominator - secondDenominator‖ / gap ^ 2 := by
  have firstNonzero : firstDenominator ≠ 0 := norm_pos_iff.mp (gapPositive.trans_le firstSeparated)
  have secondNonzero : secondDenominator ≠ 0 := norm_pos_iff.mp (gapPositive.trans_le secondSeparated)
  have identity : firstNumerator / firstDenominator - secondNumerator / secondDenominator =
      (firstNumerator - secondNumerator) / firstDenominator +
        secondNumerator * (firstDenominator⁻¹ - secondDenominator⁻¹) := by
    simp only [div_eq_mul_inv]
    ring
  have inverseDifference : ‖firstDenominator⁻¹ - secondDenominator⁻¹‖ ≤
      ‖firstDenominator - secondDenominator‖ / gap ^ 2 := by
    have inverse := dist_inv_inv₀ firstNonzero secondNonzero
    simp only [dist_eq_norm] at inverse
    rw [inverse]
    have denominator : gap ^ 2 ≤ ‖firstDenominator‖ * ‖secondDenominator‖ := by
      simpa only [pow_two] using mul_le_mul firstSeparated secondSeparated gapPositive.le (norm_nonneg _)
    exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos gapPositive) denominator
  rw [identity]
  apply (norm_add_le _ _).trans
  rw [norm_div, norm_mul]
  exact add_le_add
    (div_le_div_of_nonneg_left (norm_nonneg _) gapPositive firstSeparated)
    ((mul_le_mul_of_nonneg_left inverseDifference (norm_nonneg secondNumerator)).trans_eq (by ring))

end EulerNonuniqueness.General
