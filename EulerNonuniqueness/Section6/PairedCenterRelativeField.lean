import EulerNonuniqueness.Section6.PairedCenterFieldBound
import EulerNonuniqueness.General.QuotientDifferenceBound

noncomputable section

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 4000000

theorem complex_inverse_pair_relative_norm_le (firstLeft firstRight secondLeft secondRight : ℂ)
    {gap radius : ℝ} (gapPositive : 0 < gap)
    (firstLeftSeparated : gap ≤ ‖firstLeft‖) (firstRightSeparated : gap ≤ ‖firstRight‖)
    (secondLeftSeparated : gap ≤ ‖secondLeft‖) (secondRightSeparated : gap ≤ ‖secondRight‖)
    (firstLeftBound : ‖firstLeft‖ ≤ radius) (secondRightBound : ‖secondRight‖ ≤ radius) :
    ‖(firstLeft⁻¹ + firstRight⁻¹) - (secondLeft⁻¹ + secondRight⁻¹)‖ ≤
      ‖(firstLeft + firstRight) - (secondLeft + secondRight)‖ / gap ^ 2 +
        ‖secondLeft + secondRight‖ * radius *
          (‖firstLeft - secondLeft‖ + ‖firstRight - secondRight‖) / gap ^ 4 := by
  have pairIdentity (left right : ℂ) (leftSeparated : gap ≤ ‖left‖) (rightSeparated : gap ≤ ‖right‖) :
      left⁻¹ + right⁻¹ = (left + right) / (left * right) := by
    have leftNonzero := norm_pos_iff.mp (gapPositive.trans_le leftSeparated)
    have rightNonzero := norm_pos_iff.mp (gapPositive.trans_le rightSeparated)
    field_simp
    <;> ring
  have productLower (left right : ℂ) (leftSeparated : gap ≤ ‖left‖) (rightSeparated : gap ≤ ‖right‖) :
      gap ^ 2 ≤ ‖left * right‖ := by
    rw [norm_mul, pow_two]
    exact mul_le_mul leftSeparated rightSeparated gapPositive.le (norm_nonneg _)
  have productDifference : ‖firstLeft * firstRight - secondLeft * secondRight‖ ≤
      radius * (‖firstLeft - secondLeft‖ + ‖firstRight - secondRight‖) := by
    have identity : firstLeft * firstRight - secondLeft * secondRight =
        firstLeft * (firstRight - secondRight) + (firstLeft - secondLeft) * secondRight := by ring
    rw [identity]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    apply (add_le_add (mul_le_mul_of_nonneg_right firstLeftBound (norm_nonneg _))
      (mul_le_mul_of_nonneg_left secondRightBound (norm_nonneg _))).trans_eq
    ring
  rw [pairIdentity firstLeft firstRight firstLeftSeparated firstRightSeparated,
    pairIdentity secondLeft secondRight secondLeftSeparated secondRightSeparated]
  have actual := EulerNonuniqueness.General.norm_quotient_difference_le
    (firstLeft + firstRight) (secondLeft + secondRight) (firstLeft * firstRight) (secondLeft * secondRight)
    (sq_pos_of_pos gapPositive) (productLower _ _ firstLeftSeparated firstRightSeparated)
    (productLower _ _ secondLeftSeparated secondRightSeparated)
  apply actual.trans
  apply add_le_add_left
  have multiplied := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left productDifference (norm_nonneg (secondLeft + secondRight)))
    (sq_nonneg (gap ^ 2))
  convert multiplied using 1 <;> ring

theorem fourPointArithmeticCenter_field_relative_signedMoment_bound
    (coefficient : ℝ) (first second : FourPointConfiguration) {gap radius : ℝ}
    (gapPositive : 0 < gap) (radiusNonnegative : 0 ≤ radius)
    (firstBound : ∀ patch, ‖first patch‖ ≤ radius) (secondBound : ∀ patch, ‖second patch‖ ≤ radius)
    (firstSeparated : ∀ positive negative : Fin 4, positive.val < 2 → 2 ≤ negative.val →
      gap ≤ ‖first positive - first negative‖)
    (secondSeparated : ∀ positive negative : Fin 4, positive.val < 2 → 2 ≤ negative.val →
      gap ≤ ‖second positive - second negative‖) :
    ‖fourPointArithmeticCenter (fourPointField coefficient first) -
      fourPointArithmeticCenter (fourPointField coefficient second)‖ ≤
      |coefficient| * (‖fourPointSignedMoment first - fourPointSignedMoment second‖ / gap ^ 2 +
        8 * radius * ‖fourPointSignedMoment second‖ * ‖first - second‖ / gap ^ 4) := by
  have difference (positive negative : Fin 4) :
      ‖star (first positive - first negative) - star (second positive - second negative)‖ ≤ 2 * ‖first - second‖ := by
    rw [← star_sub, norm_star]
    have identity : (first positive - first negative) - (second positive - second negative) =
        (first positive - second positive) - (first negative - second negative) := by abel
    rw [identity]
    exact (norm_sub_le _ _).trans (by
      have left := norm_le_pi_norm (first - second) positive
      have right := norm_le_pi_norm (first - second) negative
      simp only [Pi.sub_apply] at left right
      linarith)
  have positionBound (side : FourPointConfiguration) (bounded : ∀ patch, ‖side patch‖ ≤ radius)
      (positive negative : Fin 4) : ‖star (side positive - side negative)‖ ≤ 2 * radius := by
    rw [norm_star]
    exact (norm_sub_le _ _).trans (by linarith [bounded positive, bounded negative])
  have momentIdentity (positions : FourPointConfiguration) :
      star (positions 0 - positions 2) + star (positions 1 - positions 3) = star (fourPointSignedMoment positions) ∧
      star (positions 0 - positions 3) + star (positions 1 - positions 2) = star (fourPointSignedMoment positions) := by
    constructor <;> simp [fourPointSignedMoment, fourPointSign, Fin.sum_univ_succ, star_sub] <;> ring
  have paired (leftPositive rightPositive leftNegative rightNegative : Fin 4)
      (leftPositiveBound : leftPositive.val < 2) (rightPositiveBound : rightPositive.val < 2)
      (leftNegativeBound : 2 ≤ leftNegative.val) (rightNegativeBound : 2 ≤ rightNegative.val)
      (firstIdentity : star (first leftPositive - first leftNegative) + star (first rightPositive - first rightNegative) =
        star (fourPointSignedMoment first))
      (secondIdentity : star (second leftPositive - second leftNegative) + star (second rightPositive - second rightNegative) =
        star (fourPointSignedMoment second)) :
      ‖((star (first leftPositive - first leftNegative))⁻¹ + (star (first rightPositive - first rightNegative))⁻¹) -
        ((star (second leftPositive - second leftNegative))⁻¹ + (star (second rightPositive - second rightNegative))⁻¹)‖ ≤
      ‖fourPointSignedMoment first - fourPointSignedMoment second‖ / gap ^ 2 +
        8 * radius * ‖fourPointSignedMoment second‖ * ‖first - second‖ / gap ^ 4 := by
    have actual := complex_inverse_pair_relative_norm_le
      (star (first leftPositive - first leftNegative)) (star (first rightPositive - first rightNegative))
      (star (second leftPositive - second leftNegative)) (star (second rightPositive - second rightNegative))
      gapPositive
      (by simpa only [norm_star] using firstSeparated _ _ leftPositiveBound leftNegativeBound)
      (by simpa only [norm_star] using firstSeparated _ _ rightPositiveBound rightNegativeBound)
      (by simpa only [norm_star] using secondSeparated _ _ leftPositiveBound leftNegativeBound)
      (by simpa only [norm_star] using secondSeparated _ _ rightPositiveBound rightNegativeBound)
      (positionBound first firstBound _ _) (positionBound second secondBound _ _)
    rw [firstIdentity, secondIdentity, ← star_sub, norm_star, norm_star] at actual
    apply actual.trans
    apply add_le_add_left
    have displacement := add_le_add (difference leftPositive leftNegative) (difference rightPositive rightNegative)
    have multiplied := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left displacement (show 0 ≤ ‖fourPointSignedMoment second‖ * (2 * radius) by positivity))
      (pow_nonneg gapPositive.le 4)
    convert multiplied using 1 <;> ring
  have firstPair := paired 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
    (momentIdentity first).1 (momentIdentity second).1
  have secondPair := paired 0 1 3 2 (by decide) (by decide) (by decide) (by decide)
    (momentIdentity first).2 (momentIdentity second).2
  rw [fourPointArithmeticCenter_field_cross_formula, fourPointArithmeticCenter_field_cross_formula,
    ← mul_sub, norm_mul, norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have normTwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [normTwo]
  have rearrange :
      (((star (first 0 - first 2))⁻¹ + (star (first 1 - first 3))⁻¹) +
          ((star (first 0 - first 3))⁻¹ + (star (first 1 - first 2))⁻¹)) -
        (((star (second 0 - second 2))⁻¹ + (star (second 1 - second 3))⁻¹) +
          ((star (second 0 - second 3))⁻¹ + (star (second 1 - second 2))⁻¹)) =
      (((star (first 0 - first 2))⁻¹ + (star (first 1 - first 3))⁻¹) -
        ((star (second 0 - second 2))⁻¹ + (star (second 1 - second 3))⁻¹)) +
      (((star (first 0 - first 3))⁻¹ + (star (first 1 - first 2))⁻¹) -
        ((star (second 0 - second 3))⁻¹ + (star (second 1 - second 2))⁻¹)) := by abel
  rw [rearrange]
  have sumBound := (norm_add_le _ _).trans (add_le_add firstPair secondPair)
  have estimate := mul_le_mul_of_nonneg_left sumBound (show 0 ≤ |coefficient| / 2 by positivity)
  convert estimate using 1 <;> ring

end EulerNonuniqueness.Section6
