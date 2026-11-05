import EulerNonuniqueness.Section3.C1HolderInverse

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def c1InverseUniformBound (bound lower : ℝ) : ℝ :=
  max (1 / lower) (4 * bound * (max (1 / lower) (2 * bound / lower^2))^2)

theorem c1Inverse_uniform_norm_bound (data : PeriodicC1HolderHalf) {lower bound : ℝ}
    (lower_pos : 0 < lower) (separated : ∀ label, lower ≤ ‖data.val.1 label‖)
    (bounded : ‖data‖ ≤ bound) :
    ‖c1Inverse data lower_pos separated‖ ≤ c1InverseUniformBound bound lower := by
  apply (c1Inverse_norm_bound data lower_pos separated).trans
  apply max_le_max le_rfl
  apply (c1InverseTangent_norm_bound data lower_pos separated).trans
  have bound_nonneg := (norm_nonneg data).trans bounded
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left bounded (by norm_num)
  · apply pow_le_pow_left₀ (by positivity)
    exact max_le_max le_rfl (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left bounded (by norm_num)) (sq_nonneg lower))
  · positivity
  · positivity

abbrev SeparatedC1Holder (lower : ℝ) :=
  {data : PeriodicC1HolderHalf // ∀ label, lower ≤ ‖data.val.1 label‖}

def c1InverseOnSeparated {lower : ℝ} (lower_pos : 0 < lower) (data : SeparatedC1Holder lower) :
    PeriodicC1HolderHalf := c1Inverse data.val lower_pos data.property

set_option maxHeartbeats 1000000 in
theorem c1InverseOnSeparated_locallyLipschitz {lower : ℝ} (lower_pos : 0 < lower) :
    LocallyLipschitz (c1InverseOnSeparated lower_pos) := by
  intro data
  let bound := ‖data.val‖ + 1
  have bound_nonneg : 0 ≤ bound := by dsimp only [bound]; positivity
  have inverse_bound_nonneg : 0 ≤ c1InverseUniformBound bound lower := by
    exact (by positivity : 0 ≤ 1 / lower).trans (le_max_left _ _)
  let constant : NNReal := ⟨64 * (c1InverseUniformBound bound lower)^2, by positivity⟩
  let neighborhood := {other : SeparatedC1Holder lower | ‖other.val‖ < bound}
  have neighborhood_mem : neighborhood ∈ 𝓝 data := by
    have value_continuous : Continuous (fun other : SeparatedC1Holder lower => other.val) := continuous_subtype_val
    have neighborhood_open : IsOpen neighborhood := isOpen_lt value_continuous.norm continuous_const
    have data_mem : data ∈ neighborhood := by
      change ‖data.val‖ < ‖data.val‖ + 1
      exact lt_add_one _
    exact neighborhood_open.mem_nhds data_mem
  refine ⟨constant, neighborhood, neighborhood_mem, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro first first_mem second second_mem
  have first_bound := c1Inverse_uniform_norm_bound first.val lower_pos first.property first_mem.le
  have second_bound := c1Inverse_uniform_norm_bound second.val lower_pos second.property second_mem.le
  have estimate := c1Inverse_difference_norm_bound first.val second.val lower_pos lower_pos first.property second.property
  have product := mul_le_mul first_bound second_bound (norm_nonneg _) inverse_bound_nonneg
  rw [dist_eq_norm (c1InverseOnSeparated lower_pos first) (c1InverseOnSeparated lower_pos second),
    Subtype.dist_eq, dist_eq_norm first.val second.val]
  change ‖c1Inverse first.val lower_pos first.property - c1Inverse second.val lower_pos second.property‖ ≤
    (64 * c1InverseUniformBound bound lower ^ 2) * ‖first.val - second.val‖
  nlinarith [mul_le_mul_of_nonneg_right product (norm_nonneg (first.val - second.val))]

theorem c1InverseOnSeparated_continuous {lower : ℝ} (lower_pos : 0 < lower) :
    Continuous (c1InverseOnSeparated lower_pos) :=
  (c1InverseOnSeparated_locallyLipschitz lower_pos).continuous

end

end EulerNonuniqueness.Paper
