import EulerNonuniqueness.Section1.ExternalFieldScaleBounds
import EulerNonuniqueness.Section1.DyadicSeparation

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

def Scales.individualInteractionDistance (scales : Scales) (receiver source : ℕ) : ℝ :=
  if source = receiver then scales.length receiver / 100
  else |scales.location receiver - scales.location source| / 8

theorem Scales.individualInteractionDistance_pos (scales : Scales) (receiver source : ℕ) :
    0 < scales.individualInteractionDistance receiver source := by
  unfold Scales.individualInteractionDistance
  split_ifs with same
  · exact div_pos (scales.length_pos _) (by norm_num)
  · exact div_pos (scales.location_distance_pos (Ne.symm same)) (by norm_num)

theorem Scales.individualInteractionWeight_same (scales : Scales) (index : ℕ) :
    scales.circulation index / scales.individualInteractionDistance index index ^ 2 =
      20000 * Real.pi * scales.omega index := by
  rw [Scales.individualInteractionDistance, if_pos rfl, Scales.circulation]
  have nonzero := (scales.length_pos index).ne'
  field_simp
  <;> ring

theorem Scales.individualInteractionWeight_foreign (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {receiver source : ℕ} (different : source ≠ receiver) :
    scales.circulation source / scales.individualInteractionDistance receiver source ^ 2 ≤
      576 * (scales.circulation source / scales.location source ^ 2) := by
  have locationBound := scales.location_sum_le_three_distance (Ne.symm different)
  have receiverPositive := scales.location_pos receiver
  have sourcePositive := scales.location_pos source
  have distanceLower : scales.location source / 24 ≤
      |scales.location receiver - scales.location source| / 8 := by linarith
  have squareLower := pow_le_pow_left₀ (by positivity : 0 ≤ scales.location source / 24) distanceLower 2
  rw [Scales.individualInteractionDistance, if_neg different]
  calc
    _ ≤ scales.circulation source / (scales.location source / 24) ^ 2 :=
      div_le_div_of_nonneg_left (scales.circulation_pos frequencyPositive ratioPositive _).le (by positivity) squareLower
    _ = _ := by field_simp; ring

theorem Scales.sum_individualInteractionWeight_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (receiver : Fin count) :
    (∑ source : Fin count, scales.circulation (source.val + 1) /
      scales.individualInteractionDistance (receiver.val + 1) (source.val + 1) ^ 2) ≤
      20000 * Real.pi * scales.omega (receiver.val + 1) + 576 * scales.strain := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have finiteStrain : (∑ source : Fin count,
      scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 2) ≤ scales.strain := by
    have rangeEquality : (∑ source : Fin count,
        scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 2) =
        ∑ source ∈ Finset.range count, scales.circulation (source + 1) / scales.location (source + 1) ^ 2 :=
      Fin.sum_univ_eq_sum_range (fun source : ℕ =>
        scales.circulation (source + 1) / scales.location (source + 1) ^ 2) count
    rw [rangeEquality]
    exact (scales.circulation_location_summable frequencyBound ratioBound alphaPositive 2).sum_le_tsum
      (Finset.range count) (fun source _ =>
        div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
  have comparison := Finset.sum_le_sum (s := Finset.univ) (fun (source : Fin count) _ =>
    show scales.circulation (source.val + 1) /
        scales.individualInteractionDistance (receiver.val + 1) (source.val + 1) ^ 2 ≤
      (if source = receiver then 20000 * Real.pi * scales.omega (receiver.val + 1) else 0) +
        576 * (scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 2) from by
      by_cases same : source = receiver
      · subst source
        rw [if_pos rfl, scales.individualInteractionWeight_same]
        exact le_add_of_nonneg_right (mul_nonneg (by norm_num)
          (div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)))
      · rw [if_neg same, zero_add]
        apply scales.individualInteractionWeight_foreign frequencyPositive ratioPositive
        intro equality
        exact same (Fin.ext (Nat.add_right_cancel equality)))
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ receiver), ← Finset.mul_sum] at comparison
  exact comparison.trans (add_le_add_left (mul_le_mul_of_nonneg_left finiteStrain (by norm_num)) _)

end EulerNonuniqueness.Paper
