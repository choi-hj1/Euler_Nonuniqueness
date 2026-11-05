import EulerNonuniqueness.Section5.CascadeForeignMomentBound
import EulerNonuniqueness.Section1.OuterCirculationTail

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.outer_cascade_foreign_velocity_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {factor : ℝ} (factorPositive : 0 < factor)
    (index : Fin count) (outer : index.val = 0) :
    (∑ source ∈ Finset.univ.erase index, 2 * scales.circulation (source.val + 1) /
      (Real.pi * cascadeForeignDistance scales factor index source)) ≤
        (96 / (Real.pi * factor)) * ∑' source : ℕ, scales.circulation (source + 2) := by
  have identity :
      (∑ source ∈ Finset.univ.erase index, 2 * scales.circulation (source.val + 1) /
        (Real.pi * cascadeForeignDistance scales factor index source)) =
      factor⁻¹ * (∑ source ∈ Finset.univ.erase index, 2 * scales.circulation (source.val + 1) /
        (Real.pi * (|scales.location (index.val + 1) - scales.location (source.val + 1)| / 8))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    simp only [cascadeForeignDistance, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [identity]
  have bound := mul_le_mul_of_nonneg_left
    (scales.outer_foreign_velocity_weight_le frequencyBound ratioBound alphaPositive index outer)
    (inv_nonneg.mpr factorPositive.le)
  convert bound using 1 <;> ring

end EulerNonuniqueness.Paper
