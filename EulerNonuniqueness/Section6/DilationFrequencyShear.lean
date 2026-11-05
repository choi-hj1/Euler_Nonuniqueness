import EulerNonuniqueness.Section6.DiagonalFrequencyDifference

noncomputable section

namespace EulerNonuniqueness.Section6

theorem dilation_frequency_shear_remainder_le (frequency first second : ℝ)
    (firstLower : (1 / 2 : ℝ) ≤ first) (secondLower : (1 / 2 : ℝ) ≤ second)
    (secondUpper : second ≤ 2) :
    |-(frequency / first - frequency / second) - frequency * (first - second)| ≤
      4 * |frequency| * |first - second| * (2 * |first - second| + 3 * |second - 1|) := by
  have firstPositive : 0 < first := by linarith
  have secondPositive : 0 < second := by linarith
  have productPositive : 0 < first * second := mul_pos firstPositive secondPositive
  have productLower : (1 / 4 : ℝ) ≤ first * second := by
    nlinarith [mul_nonneg (sub_nonneg.mpr firstLower) (sub_nonneg.mpr secondLower)]
  have identity : -(frequency / first - frequency / second) - frequency * (first - second) =
      frequency * (first - second) * (1 - first * second) / (first * second) := by
    field_simp
    <;> ring
  have productIdentity : first * second - 1 = (first - second) * second + (second - 1) * (second + 1) := by ring
  have productDefect : |1 - first * second| ≤ 2 * |first - second| + 3 * |second - 1| := by
    rw [abs_sub_comm, productIdentity]
    have triangle := abs_add ((first - second) * second) ((second - 1) * (second + 1))
    rw [abs_mul, abs_mul, abs_of_pos secondPositive, abs_of_pos (by linarith : 0 < second + 1)] at triangle
    have firstBound := mul_le_mul_of_nonneg_left secondUpper (abs_nonneg (first - second))
    have secondBound := mul_le_mul_of_nonneg_left (show second + 1 ≤ 3 by linarith) (abs_nonneg (second - 1))
    nlinarith
  rw [identity, abs_div, abs_mul, abs_mul, abs_of_pos productPositive]
  have numerator := mul_le_mul_of_nonneg_left productDefect
    (mul_nonneg (abs_nonneg frequency) (abs_nonneg (first - second)))
  have firstBound := div_le_div_of_nonneg_right numerator productPositive.le
  have secondBound := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ |frequency| * |first - second| * (2 * |first - second| + 3 * |second - 1|))
    (by norm_num : (0 : ℝ) < 1 / 4) productLower
  exact (firstBound.trans secondBound).trans_eq (by ring)

end EulerNonuniqueness.Section6
