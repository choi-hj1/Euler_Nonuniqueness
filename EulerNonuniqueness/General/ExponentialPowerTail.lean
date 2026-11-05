import EulerNonuniqueness.General.TwoSidedExponentialKernel

namespace EulerNonuniqueness

theorem pow_mul_exp_neg_mul_le_factorial (degree : ℕ) {rate frequency : ℝ}
    (ratePositive : 0 < rate) (frequencyNonnegative : 0 ≤ frequency) :
    frequency ^ degree * Real.exp (-rate * frequency) ≤ (degree.factorial : ℝ) / rate ^ degree := by
  have factorialPositive : 0 < (degree.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos degree
  have exponentialBound := Real.pow_div_factorial_le_exp (rate * frequency)
    (mul_nonneg ratePositive.le frequencyNonnegative) degree
  have powerBound := (div_le_iff₀ factorialPositive).mp exponentialBound
  have multiplied := mul_le_mul_of_nonneg_right powerBound (Real.exp_pos (-rate * frequency)).le
  have cancellation : Real.exp (rate * frequency) * (degree.factorial : ℝ) *
      Real.exp (-rate * frequency) = degree.factorial := by
    rw [mul_right_comm, ← Real.exp_add]
    rw [show rate * frequency + -rate * frequency = 0 by ring, Real.exp_zero, one_mul]
  rw [cancellation, mul_pow] at multiplied
  apply (le_div_iff₀ (pow_pos ratePositive degree)).mpr
  convert multiplied using 1 <;> ring

theorem exp_neg_mul_le_factorial_div_pow (degree : ℕ) {rate frequency : ℝ}
    (ratePositive : 0 < rate) (frequencyPositive : 0 < frequency) :
    Real.exp (-rate * frequency) ≤ ((degree.factorial : ℝ) / rate ^ degree) / frequency ^ degree := by
  apply (le_div_iff₀ (pow_pos frequencyPositive degree)).mpr
  simpa only [mul_comm] using pow_mul_exp_neg_mul_le_factorial degree ratePositive frequencyPositive.le

end EulerNonuniqueness
