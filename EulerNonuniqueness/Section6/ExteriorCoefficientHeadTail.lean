import EulerNonuniqueness.Section3.ExteriorCoefficientWeights

noncomputable section

namespace EulerNonuniqueness.Section6

theorem coefficient_norm_head_tail_le_tsum (coefficient : ℕ → ℂ)
    (summable : Summable (fun power => ‖coefficient power‖)) :
    ‖coefficient 0‖ ≤ ∑' power, ‖coefficient power‖ ∧
      (∑' power : ℕ, ‖coefficient (power + 1)‖) ≤ ∑' power, ‖coefficient power‖ := by
  have identity := summable.tsum_eq_zero_add
  have tailNonnegative : 0 ≤ ∑' power : ℕ, ‖coefficient (power + 1)‖ := tsum_nonneg (fun _ => norm_nonneg _)
  constructor <;> rw [identity] <;> linarith [norm_nonneg (coefficient 0)]

theorem coefficient_norm_head_tail_le_weighted_tsum (coefficient : ℕ → ℂ)
    {weight : ℝ} (weightLarge : 1 ≤ weight)
    (summable : Summable (fun power => weight ^ (power + 1) * ‖coefficient power‖)) :
    ‖coefficient 0‖ ≤ ∑' power, weight ^ (power + 1) * ‖coefficient power‖ ∧
      (∑' power : ℕ, ‖coefficient (power + 1)‖) ≤ ∑' power, weight ^ (power + 1) * ‖coefficient power‖ := by
  have pointwise (power : ℕ) : ‖coefficient power‖ ≤ weight ^ (power + 1) * ‖coefficient power‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ weightLarge)
  have unweighted := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) pointwise summable
  have comparison := unweighted.tsum_le_tsum pointwise summable
  have actual := coefficient_norm_head_tail_le_tsum coefficient unweighted
  exact ⟨actual.1.trans comparison, actual.2.trans comparison⟩

end EulerNonuniqueness.Section6
