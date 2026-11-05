import EulerNonuniqueness.Section6.RelativeShapeForcingOperatorBudget
import EulerNonuniqueness.General.QuotientDifferenceBound

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

private theorem norm_square_difference_le (first second : ℂ) {length difference : ℝ}
    (lengthNonnegative : 0 ≤ length) (differenceNonnegative : 0 ≤ difference)
    (firstBound : ‖first‖ ≤ 2 * length) (secondBound : ‖second‖ ≤ 2 * length)
    (differenceBound : ‖first - second‖ ≤ difference) :
    |‖first‖ ^ 2 - ‖second‖ ^ 2| ≤ 4 * length * difference := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have firstFactor := (abs_norm_sub_norm_le first second).trans differenceBound
  have product := mul_le_mul firstFactor (by linarith : ‖first‖ + ‖second‖ ≤ 4 * length)
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) differenceNonnegative
  nlinarith only [product]

theorem pointShapeRatio_relative_annular_bound (first second : ℂ × ℂ) {length : ℝ}
    (lengthPositive : 0 < length)
    (firstPositiveLower : length / 2 ≤ ‖first.1‖) (secondPositiveLower : length / 2 ≤ ‖second.1‖)
    (firstPositiveUpper : ‖first.1‖ ≤ 2 * length) (secondPositiveUpper : ‖second.1‖ ≤ 2 * length)
    (firstNegativeUpper : ‖first.2‖ ≤ 2 * length) (secondNegativeUpper : ‖second.2‖ ≤ 2 * length) :
    |pointShapeRatio first.1 first.2 - pointShapeRatio second.1 second.2| ≤ 272 / length * ‖first - second‖ := by
  have firstDifference : ‖first.1 - second.1‖ ≤ ‖first - second‖ := norm_fst_le (first - second)
  have secondDifference : ‖first.2 - second.2‖ ≤ ‖first - second‖ := norm_snd_le (first - second)
  have numerator := norm_square_difference_le first.2 second.2 lengthPositive.le (norm_nonneg _)
    firstNegativeUpper secondNegativeUpper secondDifference
  have denominator := norm_square_difference_le first.1 second.1 lengthPositive.le (norm_nonneg _)
    firstPositiveUpper secondPositiveUpper firstDifference
  have firstGap : length ^ 2 / 4 ≤ ‖‖first.1‖ ^ 2‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg first.1]
  have secondGap : length ^ 2 / 4 ≤ ‖‖second.1‖ ^ 2‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg second.1]
  have actual := EulerNonuniqueness.General.norm_quotient_difference_le
    (‖first.2‖ ^ 2) (‖second.2‖ ^ 2) (‖first.1‖ ^ 2) (‖second.1‖ ^ 2)
    (by positivity : 0 < length ^ 2 / 4) firstGap secondGap
  simp only [Real.norm_eq_abs, abs_sq] at actual
  have referenceSquare : ‖second.2‖ ^ 2 ≤ 4 * length ^ 2 := by nlinarith [norm_nonneg second.2]
  have enlarged := actual.trans (add_le_add (div_le_div_of_nonneg_right numerator (by positivity))
    (div_le_div_of_nonneg_right (mul_le_mul referenceSquare denominator (abs_nonneg _)
      (by positivity : 0 ≤ 4 * length ^ 2)) (by positivity)))
  change |pointShapeRatio first.1 first.2 - pointShapeRatio second.1 second.2| ≤ _ at enlarged
  exact enlarged.trans_eq (by field_simp [lengthPositive.ne']; ring)

private theorem inverse_difference_annular_bound (first second : ℂ) {gap difference : ℝ}
    (gapPositive : 0 < gap) (firstBound : gap ≤ ‖first‖) (secondBound : gap ≤ ‖second‖)
    (differenceBound : ‖first - second‖ ≤ difference) :
    ‖first⁻¹ - second⁻¹‖ ≤ difference / gap ^ 2 := by
  have actual := EulerNonuniqueness.General.norm_quotient_difference_le (1 : ℂ) 1 first second
    gapPositive firstBound secondBound
  simpa only [one_div, sub_self, norm_zero, norm_one, zero_div, zero_add, one_mul] using
    actual.trans (add_le_add_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left differenceBound (norm_nonneg (1 : ℂ)))
      (sq_nonneg gap)) _)

theorem pointShapeForcingOperatorVariation_annular_bound (first second : ℂ × ℂ) {length : ℝ}
    (lengthPositive : 0 < length)
    (firstPositiveLower : length / 2 ≤ ‖first.1‖) (secondPositiveLower : length / 2 ≤ ‖second.1‖)
    (firstNegativeLower : length / 8 ≤ ‖first.2‖) (secondNegativeLower : length / 8 ≤ ‖second.2‖)
    (firstPositiveUpper : ‖first.1‖ ≤ 2 * length) (secondPositiveUpper : ‖second.1‖ ≤ 2 * length)
    (firstNegativeUpper : ‖first.2‖ ≤ 2 * length) (secondNegativeUpper : ‖second.2‖ ≤ 2 * length)
    (radialBound : pointShapeRatio first.1 first.2 / rhombusRatio + 1 ≤ 3) :
    pointShapeForcingOperatorVariation first second ≤ 32844 / length ^ 2 * ‖first - second‖ := by
  have firstDifference := norm_fst_le (first - second)
  have secondDifference := norm_snd_le (first - second)
  have positiveInverse := inverse_difference_annular_bound first.1 second.1
    (by positivity : 0 < length / 2) firstPositiveLower secondPositiveLower firstDifference
  have negativeInverse := inverse_difference_annular_bound first.2 second.2
    (by positivity : 0 < length / 8) firstNegativeLower secondNegativeLower secondDifference
  have referencePositive : 0 < ‖second.1‖ := (by positivity : 0 < length / 2).trans_le secondPositiveLower
  have referenceNegative : 0 < ‖second.2‖ := (by positivity : 0 < length / 8).trans_le secondNegativeLower
  have referenceInversePositive : ‖second.1⁻¹‖ ≤ 2 / length := by
    rw [norm_inv]
    calc
      _ ≤ (length / 2)⁻¹ := (inv_le_inv₀ referencePositive (by positivity)).mpr secondPositiveLower
      _ = 2 / length := by field_simp
  have referenceInverseNegative : ‖second.2⁻¹‖ ≤ 8 / length := by
    rw [norm_inv]
    calc
      _ ≤ (length / 8)⁻¹ := (inv_le_inv₀ referenceNegative (by positivity)).mpr secondNegativeLower
      _ = 8 / length := by field_simp
  have ratio := pointShapeRatio_relative_annular_bound first second lengthPositive firstPositiveLower secondPositiveLower
    firstPositiveUpper secondPositiveUpper firstNegativeUpper secondNegativeUpper
  have rhombusLower : (1 / 12 : ℝ) ≤ rhombusRatio := by
    unfold rhombusRatio
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have normalizedRatio : |pointShapeRatio first.1 first.2 / rhombusRatio - pointShapeRatio second.1 second.2 / rhombusRatio| ≤
      3264 / length * ‖first - second‖ := by
    rw [← sub_div, abs_div, abs_of_pos rhombusRatio_pos]
    have actual := (div_le_div_of_nonneg_right ratio rhombusRatio_pos.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by norm_num : (0 : ℝ) < 1 / 12) rhombusLower)
    exact actual.trans_eq (by ring)
  have radialNonnegative : 0 ≤ pointShapeRatio first.1 first.2 / rhombusRatio + 1 := by
    unfold pointShapeRatio
    positivity
  have firstTerm := mul_le_mul radialBound (add_le_add negativeInverse positiveInverse)
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num : (0 : ℝ) ≤ 3)
  have secondTerm := mul_le_mul normalizedRatio (add_le_add referenceInverseNegative referenceInversePositive)
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
  exact (add_le_add firstTerm secondTerm).trans_eq (by
    change _ = 32844 / length ^ 2 * ‖first - second‖
    field_simp [lengthPositive.ne']
    <;> ring)

end EulerNonuniqueness.Section6
