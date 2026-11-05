import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.outer_foreign_circulation_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (index : Fin count) (outer : index.val = 0) :
    (∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1)) ≤
      ∑' source : ℕ, scales.circulation (source + 2) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have summable : Summable (fun source : ℕ => scales.circulation (source + 1)) := by
    simpa only [pow_zero, div_one] using
      scales.circulation_location_summable frequencyBound ratioBound alphaPositive 0
  have finiteBound : (∑ source : Fin count, scales.circulation (source.val + 1)) ≤
      ∑' source : ℕ, scales.circulation (source + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun source : ℕ => scales.circulation (source + 1)) count]
    exact summable.sum_le_tsum _ (fun source _ => (scales.circulation_pos frequencyPositive ratioPositive _).le)
  have erased := Finset.sum_erase_add (s := Finset.univ)
    (f := fun source : Fin count => scales.circulation (source.val + 1)) (Finset.mem_univ index)
  have decomposition := summable.tsum_eq_zero_add
  simp only [outer, zero_add] at erased
  simp only [zero_add, Nat.add_assoc] at decomposition
  linarith only [finiteBound, erased, decomposition]

theorem Scales.outer_foreign_velocity_weight_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (index : Fin count) (outer : index.val = 0) :
    (∑ source ∈ Finset.univ.erase index, 2 * scales.circulation (source.val + 1) /
      (Real.pi * (|scales.location (index.val + 1) - scales.location (source.val + 1)| / 8))) ≤
      (96 / Real.pi) * ∑' source : ℕ, scales.circulation (source + 2) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have outerLocation : scales.location (index.val + 1) = 1 / 2 := by
    rw [outer]
    norm_num [Scales.location]
  have individual (source : Fin count) (member : source ∈ Finset.univ.erase index) :
      2 * scales.circulation (source.val + 1) /
          (Real.pi * (|scales.location (index.val + 1) - scales.location (source.val + 1)| / 8)) ≤
        (96 / Real.pi) * scales.circulation (source.val + 1) := by
    have different : index.val + 1 ≠ source.val + 1 := fun equality =>
      (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm)
    have locations := scales.location_sum_le_three_distance different
    have distanceLower : (1 : ℝ) / 48 ≤
        |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8 := by
      rw [outerLocation] at locations ⊢
      linarith only [locations, (scales.location_pos (source.val + 1)).le]
    calc
      _ ≤ 2 * scales.circulation (source.val + 1) / (Real.pi * (1 / 48)) :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _).le)
          (by positivity) (mul_le_mul_of_nonneg_left distanceLower Real.pi_pos.le)
      _ = _ := by ring
  calc
    _ ≤ ∑ source ∈ Finset.univ.erase index, (96 / Real.pi) * scales.circulation (source.val + 1) :=
      Finset.sum_le_sum individual
    _ = (96 / Real.pi) * ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (scales.outer_foreign_circulation_le frequencyBound ratioBound alphaPositive index outer) (by positivity)

end EulerNonuniqueness.Paper
