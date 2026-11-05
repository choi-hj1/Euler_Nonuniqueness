import Mathlib

noncomputable section

namespace EulerNonuniqueness

theorem exists_polynomial_exponential_bound (degree : ℕ) {rate : ℝ} (ratePositive : 0 < rate) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ time : ℝ, 0 ≤ time →
      (1 + time) ^ degree ≤ bound * Real.exp (rate * time) := by
  let coefficient := (degree.factorial : ℝ) / rate ^ degree * Real.exp rate
  refine ⟨max 1 coefficient, le_max_left _ _, ?_⟩
  intro time timeNonnegative
  have factorialPositive : 0 < (degree.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos degree
  have powerPositive : 0 < rate ^ degree := pow_pos ratePositive degree
  have estimate := Real.pow_div_factorial_le_exp (rate * (1 + time))
    (show 0 ≤ rate * (1 + time) by positivity) degree
  have powerBound : rate ^ degree * (1 + time) ^ degree ≤
      Real.exp (rate * (1 + time)) * degree.factorial := by
    simpa only [mul_pow] using (div_le_iff₀ factorialPositive).mp estimate
  have bound : (1 + time) ^ degree ≤
      ((degree.factorial : ℝ) / rate ^ degree) * Real.exp (rate * (1 + time)) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ powerPositive).mpr
    convert powerBound using 1 <;> ring
  have exponentialIdentity : Real.exp (rate * (1 + time)) = Real.exp rate * Real.exp (rate * time) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [exponentialIdentity] at bound
  calc
    _ ≤ coefficient * Real.exp (rate * time) := by simpa only [coefficient, mul_assoc] using bound
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

theorem exists_polynomial_exponential_tail_bound (degree : ℕ) {decay slowerDecay : ℝ}
    (rateBound : slowerDecay < decay) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ time : ℝ, 0 ≤ time →
      (1 + time) ^ degree * Real.exp (-decay * time) ≤ bound * Real.exp (-slowerDecay * time) := by
  obtain ⟨bound, boundAtLeastOne, bounded⟩ := exists_polynomial_exponential_bound degree (sub_pos.mpr rateBound)
  refine ⟨bound, boundAtLeastOne, ?_⟩
  intro time timeNonnegative
  have estimate := mul_le_mul_of_nonneg_right (bounded time timeNonnegative) (Real.exp_pos (-decay * time)).le
  have exponentialIdentity : Real.exp ((decay - slowerDecay) * time) * Real.exp (-decay * time) =
      Real.exp (-slowerDecay * time) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [mul_assoc, exponentialIdentity] using estimate

end EulerNonuniqueness
