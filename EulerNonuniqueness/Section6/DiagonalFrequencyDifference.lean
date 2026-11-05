import EulerNonuniqueness.Section4.ReferenceStatement
import EulerNonuniqueness.Section1.Scales

noncomputable section

namespace EulerNonuniqueness.Section6

theorem dilation_frequency_difference_le (frequency first second : ℝ)
    (firstLower : (1 / 2 : ℝ) ≤ first) (secondLower : (1 / 2 : ℝ) ≤ second) :
    |frequency / first - frequency / second| ≤ 4 * |frequency| * |first - second| := by
  have firstPositive : 0 < first := by linarith
  have secondPositive : 0 < second := by linarith
  have identity : frequency / first - frequency / second = frequency * (second - first) / (first * second) := by
    field_simp
    ring
  rw [identity, abs_div, abs_mul, abs_of_pos (mul_pos firstPositive secondPositive), abs_sub_comm second first]
  apply (div_le_iff₀ (mul_pos firstPositive secondPositive)).mpr
  have productLower : (1 / 4 : ℝ) ≤ first * second := by nlinarith
  have nonnegative := mul_nonneg (abs_nonneg frequency) (abs_nonneg (first - second))
  nlinarith [mul_nonneg nonnegative (sub_nonneg.mpr productLower)]

theorem dilation_frequency_deviation_le (frequency dilation : ℝ)
    (lower : (1 / 2 : ℝ) ≤ dilation) :
    |frequency / dilation - frequency| ≤ 2 * |frequency| * |dilation - 1| := by
  have positive : 0 < dilation := by linarith
  have identity : frequency / dilation - frequency = frequency * (1 - dilation) / dilation := by
    field_simp
    ring
  rw [identity, abs_div, abs_mul, abs_of_pos positive, abs_sub_comm 1 dilation]
  apply (div_le_iff₀ positive).mpr
  have nonnegative := mul_nonneg (abs_nonneg frequency) (abs_nonneg (dilation - 1))
  nlinarith [mul_nonneg nonnegative (sub_nonneg.mpr lower)]

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

theorem diagonal_frequency_difference_le {count : ℕ} (scales : Scales)
    (first second : PatchMotion count) (index : Fin count) (time : ℝ)
    (firstLower : scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference first time index)
    (secondLower : scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference second time index) :
    |scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 / diagonalDifference first time index -
      scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 / diagonalDifference second time index| ≤
      4 * |scales.omega (index.val + 1)| *
        (|diagonalDifference first time index - diagonalDifference second time index| / scales.length (index.val + 1) ^ 2) := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have squarePositive := sq_pos_of_pos lengthPositive
  have firstPositive : 0 < diagonalDifference first time index := (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le firstLower
  have secondPositive : 0 < diagonalDifference second time index := (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le secondLower
  have firstScaled : (1 / 2 : ℝ) ≤ diagonalDifference first time index / scales.length (index.val + 1) ^ 2 :=
    (le_div_iff₀ squarePositive).mpr (by linarith)
  have secondScaled : (1 / 2 : ℝ) ≤ diagonalDifference second time index / scales.length (index.val + 1) ^ 2 :=
    (le_div_iff₀ squarePositive).mpr (by linarith)
  have actual := Section6.dilation_frequency_difference_le (scales.omega (index.val + 1))
    (diagonalDifference first time index / scales.length (index.val + 1) ^ 2)
    (diagonalDifference second time index / scales.length (index.val + 1) ^ 2) firstScaled secondScaled
  have difference : diagonalDifference first time index / scales.length (index.val + 1) ^ 2 -
      diagonalDifference second time index / scales.length (index.val + 1) ^ 2 =
      (diagonalDifference first time index - diagonalDifference second time index) / scales.length (index.val + 1) ^ 2 := by ring
  rw [difference, abs_div, abs_of_pos squarePositive] at actual
  convert actual using 1 <;> field_simp <;> ring

end EulerNonuniqueness.Paper
