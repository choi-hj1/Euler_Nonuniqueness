import Mathlib

noncomputable section

namespace EulerNonuniqueness

theorem abs_log_sub_log_le_of_relative_error {first second error : ℝ}
    (firstPositive : 0 < first) (errorBound : |second - first| ≤ error)
    (small : error ≤ first / 2) :
    |Real.log second - Real.log first| ≤ 2 * error / first := by
  have errorNonnegative : 0 ≤ error := (abs_nonneg _).trans errorBound
  have lower : first / 2 ≤ second := by have := (abs_le.mp errorBound).1; linarith
  have secondPositive : 0 < second := lt_of_lt_of_le (by positivity) lower
  have logUpper (numerator denominator : ℝ) (numeratorPositive : 0 < numerator)
      (denominatorPositive : 0 < denominator) :
      Real.log numerator - Real.log denominator ≤ (numerator - denominator) / denominator := by
    have estimate := Real.log_le_sub_one_of_pos (div_pos numeratorPositive denominatorPositive)
    rw [Real.log_div numeratorPositive.ne' denominatorPositive.ne'] at estimate
    convert estimate using 1 <;> field_simp <;> ring
  apply abs_le.mpr
  constructor
  · have estimate : Real.log first - Real.log second ≤ 2 * error / first := by
      calc
        _ ≤ (first - second) / second := logUpper first second firstPositive secondPositive
        _ ≤ error / second := div_le_div_of_nonneg_right (by have := (abs_le.mp errorBound).1; linarith) secondPositive.le
        _ ≤ error / (first / 2) := div_le_div_of_nonneg_left errorNonnegative (by positivity) lower
        _ = _ := by ring
    linarith
  · calc
      _ ≤ (second - first) / first := logUpper second first secondPositive firstPositive
      _ ≤ error / first := div_le_div_of_nonneg_right (abs_le.mp errorBound).2 firstPositive.le
      _ ≤ 2 * error / first := div_le_div_of_nonneg_right (by linarith) firstPositive.le

end EulerNonuniqueness
