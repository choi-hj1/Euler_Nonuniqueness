import EulerNonuniqueness.Section4.ReferenceStatement

open Filter
open scoped BigOperators Topology

namespace EulerNonuniqueness.General

theorem tendsto_rpow_mul_exp_neg_rpow (power alpha coefficient : ℝ)
    (alpha_pos : 0 < alpha) (coefficient_pos : 0 < coefficient) :
    Tendsto (fun value : ℝ => value ^ power * Real.exp (-coefficient * value ^ alpha))
      atTop (𝓝 0) := by
  have limit := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (power / alpha) coefficient coefficient_pos).comp (tendsto_rpow_atTop alpha_pos)
  apply limit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with value value_pos
  dsimp
  rw [← Real.rpow_mul value_pos.le]
  congr 2
  field_simp [ne_of_gt alpha_pos]

end EulerNonuniqueness.General

namespace EulerNonuniqueness.Paper

theorem Scales.omega_pos (scales : Scales) (frequency_pos : 0 < scales.frequency)
    (ratio_pos : 0 < scales.ratio) (index : ℕ) : 0 < scales.omega index := by
  exact mul_pos frequency_pos (pow_pos ratio_pos index)

theorem Scales.length_pos (scales : Scales) (index : ℕ) :
    0 < scales.length index := Real.exp_pos _

theorem Scales.length_sq (scales : Scales) (index : ℕ) :
    scales.length index ^ 2 = Real.exp (-2 * scales.omega index ^ scales.alpha) := by
  rw [Scales.length, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem Scales.circulation_pos (scales : Scales) (frequency_pos : 0 < scales.frequency)
    (ratio_pos : 0 < scales.ratio) (index : ℕ) : 0 < scales.circulation index := by
  unfold Scales.circulation
  exact mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (scales.omega_pos frequency_pos ratio_pos index)) (sq_pos_of_pos (scales.length_pos index))

theorem Scales.radius_sq (scales : Scales) (amplitude_pos : 0 < scales.amplitude)
    (frequency_pos : 0 < scales.frequency) (ratio_pos : 0 < scales.ratio) (index : ℕ) :
    scales.radius index ^ 2 =
      2 * scales.length index ^ 2 / (scales.amplitude * scales.omega index ^ 3) := by
  apply Real.sq_sqrt
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg amplitude_pos.le (pow_nonneg (scales.omega_pos frequency_pos ratio_pos index).le _))

theorem Scales.radius_pos (scales : Scales) (amplitude_pos : 0 < scales.amplitude)
    (frequency_pos : 0 < scales.frequency) (ratio_pos : 0 < scales.ratio) (index : ℕ) :
    0 < scales.radius index := by
  apply Real.sqrt_pos.2
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos (scales.length_pos index)))
    (mul_pos amplitude_pos (pow_pos (scales.omega_pos frequency_pos ratio_pos index) _))

theorem Scales.patch_circulation (scales : Scales) (amplitude_pos : 0 < scales.amplitude)
    (frequency_pos : 0 < scales.frequency) (ratio_pos : 0 < scales.ratio) (index : ℕ) :
    Real.pi * scales.radius index ^ 2 * scales.amplitude * scales.omega index ^ 4 =
      scales.circulation index := by
  rw [scales.radius_sq amplitude_pos frequency_pos ratio_pos]
  unfold Scales.circulation
  field_simp [ne_of_gt amplitude_pos, ne_of_gt (scales.omega_pos frequency_pos ratio_pos index)]
  ring

theorem Scales.location_eq_inv_pow (scales : Scales) (index : ℕ) :
    scales.location index = ((2 : ℝ) ^ index)⁻¹ := by
  simp [Scales.location]

theorem Scales.location_pos (scales : Scales) (index : ℕ) : 0 < scales.location index := by
  rw [scales.location_eq_inv_pow]
  positivity

theorem Scales.adjacent_location_distance (scales : Scales) (index : ℕ) :
    |scales.location index - scales.location (index + 1)| = scales.location (index + 1) := by
  rw [scales.location_eq_inv_pow, scales.location_eq_inv_pow]
  have difference : ((2 : ℝ) ^ index)⁻¹ - ((2 : ℝ) ^ (index + 1))⁻¹ =
      ((2 : ℝ) ^ (index + 1))⁻¹ := by
    rw [pow_succ]
    field_simp
    ring
  rw [difference, abs_of_pos]
  positivity

theorem Scales.delay_term_geometric (scales : Scales) (frequency_pos : 0 < scales.frequency)
    (ratio_pos : 0 < scales.ratio) (index : ℕ) :
    scales.omega (index + 2) ^ scales.alpha / scales.omega (index + 1) =
      scales.frequency ^ (scales.alpha - 1) * scales.ratio ^ (2 * scales.alpha - 1) *
        (scales.ratio ^ (scales.alpha - 1)) ^ index := by
  have commute (power : ℕ) : (scales.ratio ^ power) ^ scales.alpha =
      (scales.ratio ^ scales.alpha) ^ power := by
    rw [← Real.rpow_natCast_mul ratio_pos.le, mul_comm (power : ℝ) scales.alpha,
      Real.rpow_mul_natCast ratio_pos.le]
  rw [Scales.omega, Scales.omega, Real.mul_rpow frequency_pos.le (pow_nonneg ratio_pos.le _),
    commute, Real.rpow_sub frequency_pos, Real.rpow_one,
    Real.rpow_sub ratio_pos (2 * scales.alpha), Real.rpow_one,
    Real.rpow_mul ratio_pos.le, Real.rpow_two,
    Real.rpow_sub ratio_pos scales.alpha, Real.rpow_one, div_pow]
  rw [commute 2]
  simp only [pow_add, pow_one, pow_two]
  field_simp
  ring

theorem Scales.delay_summable (scales : Scales) (frequency_pos : 0 < scales.frequency)
    (ratio_gt_one : 1 < scales.ratio) (alpha_lt_one : scales.alpha < 1) :
    Summable (fun index : ℕ =>
      scales.omega (index + 2) ^ scales.alpha / scales.omega (index + 1)) := by
  have ratio_pos : 0 < scales.ratio := lt_trans zero_lt_one ratio_gt_one
  have geometric := summable_geometric_of_lt_one
    (Real.rpow_nonneg ratio_pos.le (scales.alpha - 1))
    (Real.rpow_lt_one_of_one_lt_of_neg ratio_gt_one (sub_neg.mpr alpha_lt_one))
  simpa only [scales.delay_term_geometric frequency_pos ratio_pos] using
    geometric.mul_left (scales.frequency ^ (scales.alpha - 1) * scales.ratio ^ (2 * scales.alpha - 1))

theorem Scales.delay_sum (scales : Scales) (frequency_pos : 0 < scales.frequency)
    (ratio_gt_one : 1 < scales.ratio) (alpha_lt_one : scales.alpha < 1) :
    (∑' index : ℕ, scales.omega (index + 2) ^ scales.alpha / scales.omega (index + 1)) =
      scales.frequency ^ (scales.alpha - 1) * scales.ratio ^ (2 * scales.alpha - 1) /
        (1 - scales.ratio ^ (scales.alpha - 1)) := by
  have ratio_pos : 0 < scales.ratio := lt_trans zero_lt_one ratio_gt_one
  simp_rw [scales.delay_term_geometric frequency_pos ratio_pos]
  rw [tsum_mul_left, tsum_geometric_of_lt_one
    (Real.rpow_nonneg ratio_pos.le (scales.alpha - 1))
    (Real.rpow_lt_one_of_one_lt_of_neg ratio_gt_one (sub_neg.mpr alpha_lt_one))]
  rfl

theorem Scales.omega_tendsto (scales : Scales) (frequency_pos : 0 < scales.frequency)
    (ratio_gt_one : 1 < scales.ratio) : Tendsto scales.omega atTop atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt ratio_gt_one).const_mul_atTop frequency_pos

theorem Scales.weighted_length_sq_tendsto_zero (scales : Scales)
    (frequency_pos : 0 < scales.frequency) (ratio_gt_one : 1 < scales.ratio)
    (alpha_pos : 0 < scales.alpha) (power : ℝ) :
    Tendsto (fun index : ℕ => scales.omega index ^ power *
      Real.exp (-2 * scales.omega index ^ scales.alpha)) atTop (𝓝 0) := by
  exact (General.tendsto_rpow_mul_exp_neg_rpow power scales.alpha 2 alpha_pos
    (by norm_num)).comp (scales.omega_tendsto frequency_pos ratio_gt_one)

theorem Scales.inverse_omega_summable (scales : Scales)
    (ratio_gt_one : 1 < scales.ratio) :
    Summable (fun index : ℕ => (scales.omega index)⁻¹) := by
  have ratio_pos : 0 < scales.ratio := lt_trans zero_lt_one ratio_gt_one
  have geometric := summable_geometric_of_lt_one (inv_nonneg.mpr ratio_pos.le)
    ((inv_lt_one₀ ratio_pos).mpr ratio_gt_one)
  simpa only [Scales.omega, mul_inv_rev, inv_pow, mul_comm] using
    geometric.mul_left scales.frequency⁻¹

theorem Scales.weighted_length_sq_summable (scales : Scales)
    (frequency_pos : 0 < scales.frequency) (ratio_gt_one : 1 < scales.ratio)
    (alpha_pos : 0 < scales.alpha) (power : ℝ) :
    Summable (fun index : ℕ => scales.omega index ^ power *
      Real.exp (-2 * scales.omega index ^ scales.alpha)) := by
  have bound := (scales.weighted_length_sq_tendsto_zero frequency_pos ratio_gt_one
    alpha_pos (power + 1)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  apply Summable.of_norm_bounded_eventually_nat (fun index => (scales.omega index)⁻¹)
    (scales.inverse_omega_summable ratio_gt_one)
  filter_upwards [bound] with index bound
  have omega_pos := scales.omega_pos frequency_pos (lt_trans zero_lt_one ratio_gt_one) index
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.rpow_pos_of_pos omega_pos power)
    (Real.exp_pos _)), ← one_div]
  apply (le_div_iff₀ omega_pos).mpr
  rw [Real.rpow_add omega_pos, Real.rpow_one] at bound
  convert bound.le using 1
  ring

theorem Scales.delay_bound_tendsto_zero (scales : Scales)
    (alpha_lt_one : scales.alpha < 1) :
    Tendsto (fun frequency : ℝ => frequency ^ (scales.alpha - 1) *
      scales.ratio ^ (2 * scales.alpha - 1) / (1 - scales.ratio ^ (scales.alpha - 1)))
      atTop (𝓝 0) := by
  have limit := tendsto_rpow_neg_atTop (sub_pos.mpr alpha_lt_one)
  have exponent : -(1 - scales.alpha) = scales.alpha - 1 := by ring
  rw [exponent] at limit
  simpa using (limit.mul_const (scales.ratio ^ (2 * scales.alpha - 1))).div_const
    (1 - scales.ratio ^ (scales.alpha - 1))

end EulerNonuniqueness.Paper

