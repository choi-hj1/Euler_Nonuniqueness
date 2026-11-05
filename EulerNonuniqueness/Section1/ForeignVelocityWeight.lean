import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.foreign_velocity_weight_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (index : Fin count) :
    (∑ source ∈ Finset.univ.erase index, 2 * scales.circulation (source.val + 1) /
      (Real.pi * (|scales.location (index.val + 1) - scales.location (source.val + 1)| / 8))) ≤
      (48 / Real.pi) * ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1) := by
  have estimate := scales.sum_foreignInteractionWeight_le frequencyBound ratioBound alphaPositive index 1
  simp only [pow_one] at estimate
  calc
    _ = (2 / Real.pi) * (∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) /
        (|scales.location (index.val + 1) - scales.location (source.val + 1)| / 8)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro source member
      ring
    _ ≤ (2 / Real.pi) * (24 * ∑' source : ℕ,
        scales.circulation (source + 1) / scales.location (source + 1)) :=
      mul_le_mul_of_nonneg_left estimate (by positivity)
    _ = _ := by ring

end EulerNonuniqueness.Paper
