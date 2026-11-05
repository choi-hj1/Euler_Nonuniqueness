import EulerNonuniqueness.Section3.CrossContourBanach

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem c1Phase_uniform_norm_bound (data : PeriodicC1HolderHalf) {lower bound : ℝ}
    (lower_pos : 0 < lower) (separated : ∀ label, lower ≤ ‖data.val.1 label‖)
    (bounded : ‖data‖ ≤ bound) :
    ‖c1Phase data lower_pos separated‖ ≤ 8 * bound * c1InverseUniformBound bound lower := by
  have bound_nonneg := (norm_nonneg data).trans bounded
  have inverse_bound := c1Inverse_uniform_norm_bound (c1Conjugate data) lower_pos
    (fun label => by rw [c1Conjugate_value, norm_star]; exact separated label)
    ((c1Conjugate_norm_bound data).trans bounded)
  exact (c1Product_norm_bound _ _).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left bounded (by norm_num)) inverse_bound (norm_nonneg _) (by positivity))

set_option maxHeartbeats 1000000 in
theorem c1Phase_difference_norm_bound (first second : PeriodicC1HolderHalf) {lower bound : ℝ}
    (lower_pos : 0 < lower)
    (first_separated : ∀ label, lower ≤ ‖first.val.1 label‖)
    (second_separated : ∀ label, lower ≤ ‖second.val.1 label‖)
    (first_bounded : ‖first‖ ≤ bound) (second_bounded : ‖second‖ ≤ bound) :
    ‖c1Phase first lower_pos first_separated - c1Phase second lower_pos second_separated‖ ≤
      (8 * c1InverseUniformBound bound lower + 512 * bound * (c1InverseUniformBound bound lower)^2) * ‖first - second‖ := by
  let first_sep := fun label => show lower ≤ ‖(c1Conjugate first).val.1 label‖ from by
    rw [c1Conjugate_value, norm_star]
    exact first_separated label
  let second_sep := fun label => show lower ≤ ‖(c1Conjugate second).val.1 label‖ from by
    rw [c1Conjugate_value, norm_star]
    exact second_separated label
  let first_inverse := c1Inverse (c1Conjugate first) lower_pos first_sep
  let second_inverse := c1Inverse (c1Conjugate second) lower_pos second_sep
  have bound_nonneg := (norm_nonneg first).trans first_bounded
  have inverse_nonneg : 0 ≤ c1InverseUniformBound bound lower :=
    (by positivity : 0 ≤ 1 / lower).trans (le_max_left _ _)
  have first_inverse_bound : ‖first_inverse‖ ≤ c1InverseUniformBound bound lower :=
    c1Inverse_uniform_norm_bound _ lower_pos first_sep ((c1Conjugate_norm_bound first).trans first_bounded)
  have second_inverse_bound : ‖second_inverse‖ ≤ c1InverseUniformBound bound lower :=
    c1Inverse_uniform_norm_bound _ lower_pos second_sep ((c1Conjugate_norm_bound second).trans second_bounded)
  have inverse_difference : ‖first_inverse - second_inverse‖ ≤
      64 * (c1InverseUniformBound bound lower)^2 * ‖first - second‖ := by
    apply (c1Inverse_difference_norm_bound (c1Conjugate first) (c1Conjugate second)
      lower_pos lower_pos first_sep second_sep).trans
    have product := mul_le_mul first_inverse_bound second_inverse_bound (norm_nonneg _) inverse_nonneg
    have conjugate_bound := c1Conjugate_difference_norm_bound first second
    have estimate := mul_le_mul product conjugate_bound (norm_nonneg _) (by positivity)
    nlinarith
  change ‖c1Product first first_inverse - c1Product second second_inverse‖ ≤ _
  apply (c1Product_difference_norm_bound first first_inverse second second_inverse).trans
  calc
    _ ≤ 8 * ‖first - second‖ * c1InverseUniformBound bound lower +
        8 * bound * (64 * (c1InverseUniformBound bound lower)^2 * ‖first - second‖) :=
      add_le_add (mul_le_mul_of_nonneg_left first_inverse_bound (by positivity))
        (mul_le_mul (mul_le_mul_of_nonneg_left second_bounded (by norm_num)) inverse_difference
          (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem c1Constant_difference_norm_bound (first second : ℂ) :
    ‖c1Constant first - c1Constant second‖ ≤ ‖first - second‖ := by
  have identity : c1Constant first - c1Constant second = c1Constant (first - second) := by
    exact (map_sub c1ConstantCLM first second).symm
  rw [identity]
  exact c1Constant_norm_bound _

theorem crossContourDifference_norm_bound (target source : PeriodicC1HolderHalf) (label : ℝ) :
    ‖crossContourDifference target (source.val.1 label)‖ ≤ ‖target‖ + ‖source‖ := by
  exact (norm_sub_le _ _).trans (add_le_add le_rfl
    ((c1Constant_norm_bound _).trans (PeriodicC1HolderHalf.value_bound source label)))

theorem crossContourDifference_parameter_norm_bound
    (firstTarget firstSource secondTarget secondSource : PeriodicC1HolderHalf) (label : ℝ) :
    ‖crossContourDifference firstTarget (firstSource.val.1 label) -
      crossContourDifference secondTarget (secondSource.val.1 label)‖ ≤
      ‖firstTarget - secondTarget‖ + ‖firstSource - secondSource‖ := by
  have identity : crossContourDifference firstTarget (firstSource.val.1 label) -
      crossContourDifference secondTarget (secondSource.val.1 label) =
      (firstTarget - secondTarget) - (c1Constant (firstSource.val.1 label) - c1Constant (secondSource.val.1 label)) := by
    unfold crossContourDifference
    abel
  rw [identity]
  apply (norm_sub_le (firstTarget - secondTarget)
    (c1Constant (firstSource.val.1 label) - c1Constant (secondSource.val.1 label))).trans
  apply add_le_add_left
  apply (c1Constant_difference_norm_bound _ _).trans
  exact PeriodicC1HolderHalf.value_bound (firstSource - secondSource) label

theorem crossContourTangent_parameter_norm_bound (first second : PeriodicC1HolderHalf) (label : ℝ) :
    ‖c1Constant (star (first.val.2.val.1 label)) - c1Constant (star (second.val.2.val.1 label))‖ ≤
      ‖first - second‖ := by
  apply (c1Constant_difference_norm_bound _ _).trans
  rw [← star_sub, norm_star]
  exact PeriodicC1HolderHalf.speed_bound (first - second) label

end

end EulerNonuniqueness.Paper
