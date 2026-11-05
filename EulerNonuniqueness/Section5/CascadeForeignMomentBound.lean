import EulerNonuniqueness.Section1.ExternalFieldScaleBounds
import EulerNonuniqueness.Section1.DyadicSeparation

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

def cascadeForeignDistance {count : ℕ} (scales : Scales) (factor : ℝ)
    (receiver source : Fin count) : ℝ :=
  factor * |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8

theorem Scales.sum_cascadeForeignMoment_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {factor : ℝ} (factorPositive : 0 < factor)
    (receiver : Fin count) (order : ℕ) :
    (∑ source ∈ Finset.univ.erase receiver,
      scales.circulation (source.val + 1) / cascadeForeignDistance scales factor receiver source ^ order) ≤
      (24 / factor) ^ order *
        ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1) ^ order := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have individual (source : Fin count) (member : source ∈ Finset.univ.erase receiver) :
      scales.circulation (source.val + 1) / cascadeForeignDistance scales factor receiver source ^ order ≤
        (24 / factor) ^ order * (scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ order) := by
    have different : receiver.val + 1 ≠ source.val + 1 := by
      intro equal
      exact (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equal).symm)
    have sumBound := scales.location_sum_le_three_distance different
    have gapPositive := scales.location_distance_pos different
    have sourcePositive := scales.location_pos (source.val + 1)
    have distancePositive : 0 < cascadeForeignDistance scales factor receiver source := by
      unfold cascadeForeignDistance
      positivity
    have lower : scales.location (source.val + 1) ≤
        (24 / factor) * cascadeForeignDistance scales factor receiver source := by
      have identity : (24 / factor) * cascadeForeignDistance scales factor receiver source =
          3 * |scales.location (receiver.val + 1) - scales.location (source.val + 1)| := by
        unfold cascadeForeignDistance
        field_simp
        <;> ring
      rw [identity]
      linarith [scales.location_pos (receiver.val + 1)]
    have inverseBound : 1 / cascadeForeignDistance scales factor receiver source ≤
        (24 / factor) / scales.location (source.val + 1) :=
      (div_le_div_iff₀ distancePositive sourcePositive).mpr (by simpa only [one_mul] using lower)
    have powerBound := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / cascadeForeignDistance scales factor receiver source)
      inverseBound order
    have comparison := mul_le_mul_of_nonneg_left powerBound
      (scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le
    simpa only [div_pow, one_pow, div_eq_mul_inv, mul_inv_rev, inv_pow, one_mul, mul_pow, mul_assoc,
      mul_comm, mul_left_comm] using comparison
  have finiteBound : (∑ source : Fin count,
      scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ order) ≤
      ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1) ^ order := by
    have equality : (∑ source : Fin count,
        scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ order) =
        ∑ source ∈ Finset.range count,
          scales.circulation (source + 1) / scales.location (source + 1) ^ order :=
      Fin.sum_univ_eq_sum_range (fun source : ℕ =>
        scales.circulation (source + 1) / scales.location (source + 1) ^ order) count
    rw [equality]
    exact (scales.circulation_location_summable frequencyBound ratioBound alphaPositive order).sum_le_tsum
      (Finset.range count) (fun source _ => div_nonneg
        (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (scales.location_pos _).le _))
  calc
    _ ≤ ∑ source ∈ Finset.univ.erase receiver,
        (24 / factor) ^ order * (scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ order) :=
      Finset.sum_le_sum individual
    _ ≤ ∑ source : Fin count,
        (24 / factor) ^ order * (scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ order) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro source _ _
      exact mul_nonneg (pow_nonneg (by positivity) _) (div_nonneg
        (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (scales.location_pos _).le _))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left finiteBound (pow_nonneg (by positivity) _)

end EulerNonuniqueness.Paper
