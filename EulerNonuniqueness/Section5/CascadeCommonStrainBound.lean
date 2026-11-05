import EulerNonuniqueness.Section5.CascadeForeignDistanceBounds

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.sum_cascadeCommonStrain_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {factor : ℝ} (factorPositive : 0 < factor) (first second : Fin count) :
    (∑ source ∈ (Finset.univ.erase first).erase second,
      2 * scales.circulation (source.val + 1) / (Real.pi * (factor * scales.location (source.val + 1) / 24) ^ 2)) ≤
      ((2 / Real.pi) * (24 / factor) ^ 2) * scales.strain := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have coefficientNonnegative : 0 ≤ (2 / Real.pi) * (24 / factor) ^ 2 := by positivity
  have identity (source : Fin count) :
      2 * scales.circulation (source.val + 1) / (Real.pi * (factor * scales.location (source.val + 1) / 24) ^ 2) =
        ((2 / Real.pi) * (24 / factor) ^ 2) *
          (scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 2) := by
    field_simp [Real.pi_ne_zero, factorPositive.ne', (scales.location_pos (source.val + 1)).ne']
    <;> ring
  have fullBound : (∑ source : Fin count,
      scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 2) ≤ scales.strain := by
    have equality : (∑ source : Fin count,
        scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 2) =
        ∑ source ∈ Finset.range count, scales.circulation (source + 1) / scales.location (source + 1) ^ 2 :=
      Fin.sum_univ_eq_sum_range (fun source : ℕ =>
        scales.circulation (source + 1) / scales.location (source + 1) ^ 2) count
    rw [equality]
    exact (scales.circulation_location_summable frequencyBound ratioBound alphaPositive 2).sum_le_tsum
      (Finset.range count) (fun source _ => div_nonneg
        (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
  simp_rw [identity]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ coefficientNonnegative
  apply le_trans _ fullBound
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _))
  intro source _ _
  exact div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)

end EulerNonuniqueness.Paper
