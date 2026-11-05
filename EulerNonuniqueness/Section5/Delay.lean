import EulerNonuniqueness.Section5.CascadeStatement
import EulerNonuniqueness.Section1.Scales

open Filter
open scoped BigOperators Topology

namespace EulerNonuniqueness.Paper

theorem Scales.seed_pos (scales : Scales) (frequency_pos : 0 < scales.frequency)
    (ratio_pos : 0 < scales.ratio) (index : ℕ) : 0 < scales.seed index := by
  unfold Scales.seed
  rw [scales.adjacent_location_distance]
  have omega_pos := scales.omega_pos frequency_pos ratio_pos index
  have location_pos := scales.location_pos (index + 1)
  exact div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num))
    (sq_pos_of_pos (scales.circulation_pos frequency_pos ratio_pos _)))
    (by positivity)

theorem Scales.log_inverse_seed (scales : Scales) (frequency_pos : 0 < scales.frequency)
    (ratio_pos : 0 < scales.ratio) (index : ℕ) :
    Real.log (1 / scales.seed index) =
      4 * scales.omega (index + 1) ^ scales.alpha -
        4 * ((index : ℝ) + 1) * Real.log 2 - Real.log (Real.sqrt 3) - Real.log 2 +
        Real.log (Real.sqrt 2) - 2 * Real.log scales.ratio := by
  have omega_pos := scales.omega_pos frequency_pos ratio_pos index
  have next_pos := scales.omega_pos frequency_pos ratio_pos (index + 1)
  have recurrence : scales.omega (index + 1) = scales.omega index * scales.ratio := by
    simp only [Scales.omega, pow_succ]
    ring
  rw [one_div, Real.log_inv]
  rw [Scales.seed, scales.adjacent_location_distance]
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Scales.circulation, Scales.length, scales.location_eq_inv_pow, Real.log_inv,
    Real.log_exp, Nat.cast_add, Nat.cast_one]
  rw [recurrence, Real.log_mul omega_pos.ne' ratio_pos.ne']
  ring

theorem Scales.actual_delay_pos (scales : Scales)
    (frequency_pos : 0 < scales.frequency) (ratio_pos : 0 < scales.ratio)
    {sectionTime : ℝ} (sectionTime_pos : 0 < sectionTime) (index : ℕ)
    (seed_lt_one : scales.seed index < 1) : 0 < scales.delay sectionTime index := by
  have seed_pos := scales.seed_pos frequency_pos ratio_pos index
  have logarithm_pos : 0 < Real.log (1 / scales.seed index) :=
    Real.log_pos ((one_lt_div seed_pos).mpr seed_lt_one)
  unfold Scales.delay
  exact div_pos (add_pos (div_pos logarithm_pos (by positivity)) sectionTime_pos)
    (scales.omega_pos frequency_pos ratio_pos index)

theorem Scales.actual_delay_expansion (scales : Scales)
    (frequency_pos : 0 < scales.frequency) (ratio_pos : 0 < scales.ratio)
    (sectionTime : ℝ) (index : ℕ) :
    scales.delay sectionTime index =
      (4 / (2 * Real.sqrt 2)) *
        (scales.omega (index + 1) ^ scales.alpha / scales.omega index) -
      (4 * Real.log 2 / (2 * Real.sqrt 2)) *
        (((index : ℝ) + 1) / scales.omega index) +
      (sectionTime + (-Real.log (Real.sqrt 3) - Real.log 2 +
        Real.log (Real.sqrt 2) - 2 * Real.log scales.ratio) / (2 * Real.sqrt 2)) *
        (scales.omega index)⁻¹ := by
  rw [Scales.delay, scales.log_inverse_seed frequency_pos ratio_pos]
  field_simp
  ring

theorem Scales.index_inverse_omega_summable (scales : Scales)
    (ratio_gt_one : 1 < scales.ratio) :
    Summable (fun index : ℕ => ((index : ℝ) + 1) / scales.omega index) := by
  have ratio_pos : 0 < scales.ratio := lt_trans zero_lt_one ratio_gt_one
  have ratioNorm : ‖scales.ratio⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ratio_pos)]
    exact (inv_lt_one₀ ratio_pos).mpr ratio_gt_one
  have weighted := (hasSum_coe_mul_geometric_of_norm_lt_one ratioNorm).summable
  have geometric := summable_geometric_of_norm_lt_one ratioNorm
  convert (weighted.add geometric).mul_left scales.frequency⁻¹ using 1
  ext index
  simp only [Scales.omega, div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem Scales.actual_delay_summable (scales : Scales)
    (frequency_pos : 0 < scales.frequency) (ratio_gt_one : 1 < scales.ratio)
    (alpha_lt_one : scales.alpha < 1) (sectionTime : ℝ) :
    Summable (fun index : ℕ => scales.delay sectionTime (index + 1)) := by
  have ratio_pos : 0 < scales.ratio := lt_trans zero_lt_one ratio_gt_one
  have weighted := (scales.index_inverse_omega_summable ratio_gt_one).comp_injective
    (show Function.Injective (fun index : ℕ => index + 1) from fun _ _ equal => Nat.add_right_cancel equal)
  have inverse := (scales.inverse_omega_summable ratio_gt_one).comp_injective
    (show Function.Injective (fun index : ℕ => index + 1) from fun _ _ equal => Nat.add_right_cancel equal)
  have leading := (scales.delay_summable frequency_pos ratio_gt_one alpha_lt_one).mul_left
    (4 / (2 * Real.sqrt 2))
  have affine := weighted.mul_left (4 * Real.log 2 / (2 * Real.sqrt 2))
  have constant := inverse.mul_left (sectionTime + (-Real.log (Real.sqrt 3) - Real.log 2 +
    Real.log (Real.sqrt 2) - 2 * Real.log scales.ratio) / (2 * Real.sqrt 2))
  convert (leading.sub affine).add constant using 1
  ext index
  exact scales.actual_delay_expansion frequency_pos ratio_pos sectionTime (index + 1)

theorem Scales.actual_delay_total_tendsto_zero (scales : Scales)
    (ratio_gt_one : 1 < scales.ratio) (alpha_lt_one : scales.alpha < 1)
    (sectionTime : ℝ) :
    Tendsto (fun frequency : ℝ =>
      ∑' index : ℕ, ({scales with frequency := frequency}).delay sectionTime (index + 1))
      atTop (𝓝 0) := by
  let unit : Scales := {scales with frequency := 1}
  let leading : ℕ → ℝ := fun index =>
    (4 / (2 * Real.sqrt 2)) *
      (unit.omega (index + 2) ^ scales.alpha / unit.omega (index + 1))
  have ratio_pos : 0 < scales.ratio := lt_trans zero_lt_one ratio_gt_one
  have leadingSummable : Summable leading :=
    (unit.delay_summable zero_lt_one ratio_gt_one alpha_lt_one).mul_left _
  have unitSummable := unit.actual_delay_summable zero_lt_one ratio_gt_one alpha_lt_one sectionTime
  have remainderSummable : Summable (fun index => unit.delay sectionTime (index + 1) - leading index) :=
    unitSummable.sub leadingSummable
  have termEquality (frequency : ℝ) (frequency_pos : 0 < frequency) (index : ℕ) :
      ({scales with frequency := frequency}).delay sectionTime (index + 1) =
        frequency ^ (scales.alpha - 1) * leading index +
          frequency⁻¹ * (unit.delay sectionTime (index + 1) - leading index) := by
    have changed := Scales.actual_delay_expansion ({scales with frequency := frequency})
      frequency_pos ratio_pos sectionTime (index + 1)
    rw [changed, unit.actual_delay_expansion zero_lt_one ratio_pos sectionTime (index + 1)]
    simp only [leading, unit, Scales.omega, one_mul]
    rw [Real.mul_rpow frequency_pos.le (pow_nonneg ratio_pos.le _),
      Real.rpow_sub frequency_pos, Real.rpow_one]
    field_simp
    ring
  have sumEquality (frequency : ℝ) (frequency_pos : 0 < frequency) :
      (∑' index : ℕ, ({scales with frequency := frequency}).delay sectionTime (index + 1)) =
        frequency ^ (scales.alpha - 1) * (∑' index : ℕ, leading index) +
          frequency⁻¹ * (∑' index : ℕ, (unit.delay sectionTime (index + 1) - leading index)) := by
    simp_rw [termEquality frequency frequency_pos]
    rw [Summable.tsum_add (leadingSummable.mul_left _) (remainderSummable.mul_left _)]
    simp only [tsum_mul_left]
  have powerLimit : Tendsto (fun frequency : ℝ => frequency ^ (scales.alpha - 1)) atTop (𝓝 0) := by
    have limit := tendsto_rpow_neg_atTop (sub_pos.mpr alpha_lt_one)
    have exponent : -(1 - scales.alpha) = scales.alpha - 1 := by ring
    simpa only [exponent] using limit
  have inverseLimit : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have combined := (powerLimit.mul_const (∑' index : ℕ, leading index)).add
    (inverseLimit.mul_const (∑' index : ℕ, (unit.delay sectionTime (index + 1) - leading index)))
  simp only [zero_mul, zero_add] at combined
  apply combined.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with frequency positive
  exact (sumEquality frequency positive).symm

theorem Scales.eventually_actual_delay_total_lt (scales : Scales)
    (ratio_gt_one : 1 < scales.ratio) (alpha_lt_one : scales.alpha < 1)
    (sectionTime : ℝ) {tolerance : ℝ} (tolerance_pos : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop,
      (∑' index : ℕ, ({scales with frequency := frequency}).delay sectionTime (index + 1)) <
        tolerance :=
  (scales.actual_delay_total_tendsto_zero ratio_gt_one alpha_lt_one sectionTime).eventually
    (gt_mem_nhds tolerance_pos)

end EulerNonuniqueness.Paper
