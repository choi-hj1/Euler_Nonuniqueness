import Mathlib

namespace EulerNonuniqueness.Section6

theorem memory_determinant_lower_bound {gain chart smallness : ℝ}
    (gainNonnegative : 0 ≤ gain) (chartNonnegative : 0 ≤ chart)
    (smallnessNonnegative : 0 ≤ smallness) (smallnessBound : smallness ≤ 1)
    (chartBound : gain * chart ≤ (1 / 8 : ℝ))
    (linearSmallness : gain * smallness ≤ (1 / 64 : ℝ))
    (quadraticSmallness : gain ^ 2 * smallness ≤ (1 / 64 : ℝ)) :
    (3 / 4 : ℝ) ≤ 1 - gain * (chart + smallness) ∧
      (3 / 4 : ℝ) ≤ 1 - 2 * gain * smallness ∧
      (1 / 2 : ℝ) ≤ (1 - gain * (chart + smallness)) * (1 - 2 * gain * smallness) -
        (2 * gain * smallness) * (gain * (1 + smallness)) := by
  have firstDiagonal : (3 / 4 : ℝ) ≤ 1 - gain * (chart + smallness) := by nlinarith
  have secondDiagonal : (3 / 4 : ℝ) ≤ 1 - 2 * gain * smallness := by nlinarith
  refine ⟨firstDiagonal, secondDiagonal, ?_⟩
  have productBound := mul_le_mul firstDiagonal secondDiagonal (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by linarith : 0 ≤ 1 - gain * (chart + smallness))
  have returnedBound : (2 * gain * smallness) * (gain * (1 + smallness)) ≤ (1 / 16 : ℝ) := by
    have estimate := mul_le_mul_of_nonneg_left (show 1 + smallness ≤ (2 : ℝ) by linarith)
      (by positivity : 0 ≤ 2 * gain ^ 2 * smallness)
    nlinarith
  nlinarith

end EulerNonuniqueness.Section6
