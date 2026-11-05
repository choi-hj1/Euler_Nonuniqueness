import EulerNonuniqueness.Section1.IndividualPatchInteractionWeight

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.sum_foreignInteractionWeight_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (receiver : Fin count) (power : ℕ) :
    (∑ source ∈ Finset.univ.erase receiver, scales.circulation (source.val + 1) /
      (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ power) ≤
      (24 : ℝ) ^ power * ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1) ^ power := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have termNonnegative (source : Fin count) :
      0 ≤ scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ power :=
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  have finiteBound : (∑ source : Fin count,
      scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ power) ≤
      ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1) ^ power := by
    have rangeEquality : (∑ source : Fin count,
        scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ power) =
        ∑ source ∈ Finset.range count, scales.circulation (source + 1) / scales.location (source + 1) ^ power :=
      Fin.sum_univ_eq_sum_range (fun source : ℕ =>
        scales.circulation (source + 1) / scales.location (source + 1) ^ power) count
    rw [rangeEquality]
    exact (scales.circulation_location_summable frequencyBound ratioBound alphaPositive power).sum_le_tsum
      (Finset.range count) (fun source _ => div_nonneg
        (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (scales.location_pos _).le _))
  have comparison : (∑ source ∈ Finset.univ.erase receiver, scales.circulation (source.val + 1) /
      (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ power) ≤
      ∑ source ∈ Finset.univ.erase receiver,
        (24 : ℝ) ^ power * (scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ power) := by
    apply Finset.sum_le_sum
    intro source member
    have different : receiver.val + 1 ≠ source.val + 1 := by
      intro equality
      exact (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm)
    have locations := scales.location_sum_le_three_distance different
    have distanceLower : scales.location (source.val + 1) / 24 ≤
        |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8 := by
      linarith [scales.location_pos (receiver.val + 1)]
    calc
      _ ≤ scales.circulation (source.val + 1) / (scales.location (source.val + 1) / 24) ^ power :=
        div_le_div_of_nonneg_left (scales.circulation_pos frequencyPositive ratioPositive _).le
          (pow_pos (div_pos (scales.location_pos _) (by norm_num)) _)
          (pow_le_pow_left₀ (div_nonneg (scales.location_pos _).le (by norm_num)) distanceLower power)
      _ = _ := by rw [div_pow]; field_simp; ring
  rw [← Finset.mul_sum] at comparison
  apply comparison.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun source _ _ => termNonnegative source)).trans finiteBound

theorem Scales.foreign_strain_weight_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (receiver : Fin count) :
    (∑ source ∈ Finset.univ.erase receiver,
      2 * scales.circulation (source.val + 1) /
        (Real.pi * (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 2)) ≤
      (1152 / Real.pi) * scales.strain := by
  have bound := mul_le_mul_of_nonneg_left
    (scales.sum_foreignInteractionWeight_le frequencyBound ratioBound alphaPositive receiver 2)
    (by positivity : (0 : ℝ) ≤ 2 / Real.pi)
  have identity : (∑ source ∈ Finset.univ.erase receiver,
      2 * scales.circulation (source.val + 1) /
        (Real.pi * (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 2)) =
      (2 / Real.pi) * ∑ source ∈ Finset.univ.erase receiver, scales.circulation (source.val + 1) /
        (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    ring
  rw [identity]
  exact bound.trans_eq (by unfold Scales.strain; norm_num; ring)

theorem Scales.foreign_hessian_weight_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (receiver : Fin count) :
    (∑ source ∈ Finset.univ.erase receiver,
      4 * scales.circulation (source.val + 1) /
        (Real.pi * (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 3)) ≤
      (55296 / Real.pi) * scales.hessian := by
  have bound := mul_le_mul_of_nonneg_left
    (scales.sum_foreignInteractionWeight_le frequencyBound ratioBound alphaPositive receiver 3)
    (by positivity : (0 : ℝ) ≤ 4 / Real.pi)
  have identity : (∑ source ∈ Finset.univ.erase receiver,
      4 * scales.circulation (source.val + 1) /
        (Real.pi * (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 3)) =
      (4 / Real.pi) * ∑ source ∈ Finset.univ.erase receiver, scales.circulation (source.val + 1) /
        (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 3 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    ring
  rw [identity]
  exact bound.trans_eq (by unfold Scales.hessian; norm_num; ring)

end EulerNonuniqueness.Paper
