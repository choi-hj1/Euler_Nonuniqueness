import EulerNonuniqueness.Section6.FourPointTranslationControl

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointArithmeticCenter_field_cross_formula (coefficient : ℝ) (positions : FourPointConfiguration) :
    fourPointArithmeticCenter (fourPointField coefficient positions) =
      -(Complex.I * (coefficient : ℂ) / 2) *
        (((star (positions 0 - positions 2))⁻¹ + (star (positions 1 - positions 3))⁻¹) +
          ((star (positions 0 - positions 3))⁻¹ + (star (positions 1 - positions 2))⁻¹)) := by
  have reverse (first second : Fin 4) :
      ((starRingEnd ℂ) (positions second) - (starRingEnd ℂ) (positions first))⁻¹ =
        -((starRingEnd ℂ) (positions first) - (starRingEnd ℂ) (positions second))⁻¹ := by
    rw [show (starRingEnd ℂ) (positions second) - (starRingEnd ℂ) (positions first) =
      -((starRingEnd ℂ) (positions first) - (starRingEnd ℂ) (positions second)) by ring, inv_neg]
  simp [fourPointArithmeticCenter, fourPointField, fourPointSign, Fin.sum_univ_succ, star_sub, div_eq_mul_inv]
  rw [reverse 0 1, reverse 0 2, reverse 0 3, reverse 1 2, reverse 1 3, reverse 2 3]
  ring

theorem complex_inverse_pair_norm_le {first second : ℂ} {gap : ℝ}
    (gapPositive : 0 < gap) (firstBound : gap ≤ ‖first‖) (secondBound : gap ≤ ‖second‖) :
    ‖first⁻¹ + second⁻¹‖ ≤ ‖first + second‖ / gap ^ 2 := by
  have firstNonzero : first ≠ 0 := norm_pos_iff.mp (gapPositive.trans_le firstBound)
  have secondNonzero : second ≠ 0 := norm_pos_iff.mp (gapPositive.trans_le secondBound)
  have identity : first⁻¹ + second⁻¹ = (first + second) / (first * second) := by
    field_simp
    <;> ring
  rw [identity, norm_div, norm_mul]
  have denominator := mul_le_mul firstBound secondBound gapPositive.le (norm_nonneg first)
  rw [← pow_two] at denominator
  exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos gapPositive) denominator

theorem fourPointArithmeticCenter_field_signedMoment_gap_bound
    (coefficient : ℝ) (positions : FourPointConfiguration) {gap : ℝ} (gapPositive : 0 < gap)
    (crossSeparated : ∀ positive negative : Fin 4, positive.val < 2 → 2 ≤ negative.val →
      gap ≤ ‖positions positive - positions negative‖) :
    ‖fourPointArithmeticCenter (fourPointField coefficient positions)‖ ≤
      |coefficient| * ‖fourPointSignedMoment positions‖ / gap ^ 2 := by
  have firstPair := complex_inverse_pair_norm_le
    (first := star (positions 0 - positions 2)) (second := star (positions 1 - positions 3)) gapPositive
    (by simpa only [norm_star] using crossSeparated 0 2 (by decide) (by decide))
    (by simpa only [norm_star] using crossSeparated 1 3 (by decide) (by decide))
  have secondPair := complex_inverse_pair_norm_le
    (first := star (positions 0 - positions 3)) (second := star (positions 1 - positions 2)) gapPositive
    (by simpa only [norm_star] using crossSeparated 0 3 (by decide) (by decide))
    (by simpa only [norm_star] using crossSeparated 1 2 (by decide) (by decide))
  have firstIdentity : star (positions 0 - positions 2) + star (positions 1 - positions 3) =
      star (fourPointSignedMoment positions) := by
    simp [fourPointSignedMoment, fourPointSign, Fin.sum_univ_succ, star_sub]
    ring
  have secondIdentity : star (positions 0 - positions 3) + star (positions 1 - positions 2) =
      star (fourPointSignedMoment positions) := by
    simp [fourPointSignedMoment, fourPointSign, Fin.sum_univ_succ, star_sub]
    ring
  rw [firstIdentity, norm_star] at firstPair
  rw [secondIdentity, norm_star] at secondPair
  rw [fourPointArithmeticCenter_field_cross_formula, norm_mul, norm_neg, norm_div, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have normTwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [normTwo]
  have sumBound := (norm_add_le
    ((star (positions 0 - positions 2))⁻¹ + (star (positions 1 - positions 3))⁻¹)
    ((star (positions 0 - positions 3))⁻¹ + (star (positions 1 - positions 2))⁻¹)).trans
      (add_le_add firstPair secondPair)
  have estimate := mul_le_mul_of_nonneg_left sumBound (by positivity : 0 ≤ |coefficient| / 2)
  convert estimate using 1 <;> ring

end EulerNonuniqueness.Section6
