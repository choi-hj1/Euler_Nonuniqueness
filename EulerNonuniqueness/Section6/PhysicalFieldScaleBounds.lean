import EulerNonuniqueness.Section1.ExternalFieldScaleBounds

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.finite_external_location_sum_le_total (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {count : ℕ} (index : Fin count) (order : ℕ) :
    (∑ source ∈ Finset.univ.erase index,
      scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ order) ≤
      ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1) ^ order := by
  have nonnegative (source : ℕ) : 0 ≤ scales.circulation (source + 1) / scales.location (source + 1) ^ order :=
    div_nonneg (scales.circulation_pos (zero_lt_one.trans_le frequencyBound)
      (by linarith) _).le (pow_nonneg (scales.location_pos _).le _)
  have finiteBound : (∑ source ∈ Finset.univ.erase index,
      scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ order) ≤
      ∑ source : Fin count, scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ order :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun source _ _ => nonnegative source.val)
  have comparison := Summable.tsum_le_tsum_of_inj (fun source : Fin count => source.val)
    Fin.val_injective (fun source _ => nonnegative source) (fun _ => le_rfl)
    (hasSum_fintype (fun source : Fin count =>
      scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ order)).summable
    (scales.circulation_location_summable frequencyBound ratioBound alphaPositive order)
  exact finiteBound.trans (by simpa only [tsum_fintype] using comparison)

theorem Scales.finite_external_strain_coefficient_le (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {count : ℕ} (index : Fin count) :
    (∑ source ∈ Finset.univ.erase index,
      2 * scales.circulation (source.val + 1) /
        (Real.pi * (scales.location (source.val + 1) / 16) ^ 2)) ≤ (512 / Real.pi) * scales.strain := by
  have identity : (∑ source ∈ Finset.univ.erase index,
      2 * scales.circulation (source.val + 1) /
        (Real.pi * (scales.location (source.val + 1) / 16) ^ 2)) =
      (512 / Real.pi) * ∑ source ∈ Finset.univ.erase index,
        scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    ring
  rw [identity]
  exact mul_le_mul_of_nonneg_left (scales.finite_external_location_sum_le_total
    frequencyBound ratioBound alphaPositive index 2) (by positivity)

theorem Scales.finite_external_hessian_coefficient_le (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {count : ℕ} (index : Fin count) :
    (∑ source ∈ Finset.univ.erase index,
      4 * scales.circulation (source.val + 1) /
        (Real.pi * (scales.location (source.val + 1) / 16) ^ 3)) ≤ (16384 / Real.pi) * scales.hessian := by
  have identity : (∑ source ∈ Finset.univ.erase index,
      4 * scales.circulation (source.val + 1) /
        (Real.pi * (scales.location (source.val + 1) / 16) ^ 3)) =
      (16384 / Real.pi) * ∑ source ∈ Finset.univ.erase index,
        scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 3 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    ring
  rw [identity]
  exact mul_le_mul_of_nonneg_left (scales.finite_external_location_sum_le_total
    frequencyBound ratioBound alphaPositive index 3) (by positivity)

end EulerNonuniqueness.Paper
