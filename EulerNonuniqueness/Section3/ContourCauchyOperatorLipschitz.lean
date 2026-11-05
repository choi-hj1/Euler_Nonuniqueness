import EulerNonuniqueness.Section3.ContourCauchyLipschitz

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem contourCauchyParameterOperatorConstant_nonneg {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourCauchyParameterOperatorConstant radius :=
  (contourCauchyParameterSupConstant_nonneg radius_nonneg radius_small).trans (le_max_left _ _)

theorem contourCauchyOperatorCLM_parameter_norm_bound (first second : PeriodicC1HolderHalf)
    {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius) :
    ‖contourCauchyOperatorCLM first (first_near.trans_lt radius_small) -
      contourCauchyOperatorCLM second (second_near.trans_lt radius_small)‖ ≤
      contourCauchyParameterOperatorConstant radius * ‖first - second‖ := by
  have constant_nonneg := contourCauchyParameterOperatorConstant_nonneg radius_nonneg radius_small
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro density
  exact contourCauchyOperator_parameter_norm_bound first second density radius_nonneg radius_small first_near second_near

theorem standardCircleBanach_small : ‖standardCircleBanach - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
  rw [sub_self standardCircleBanach, norm_zero]
  exact lt_min (by norm_num) (by positivity)

noncomputable def contourCauchyUniformOperatorConstant (radius : ℝ) : ℝ :=
  contourCauchyParameterOperatorConstant radius * radius +
    ‖contourCauchyOperatorCLM standardCircleBanach standardCircleBanach_small‖

theorem contourCauchyUniformOperatorConstant_nonneg {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourCauchyUniformOperatorConstant radius := by
  have constant_nonneg := contourCauchyParameterOperatorConstant_nonneg radius_nonneg radius_small
  unfold contourCauchyUniformOperatorConstant
  positivity

theorem contourCauchyOperatorCLM_uniform_norm_bound (data : PeriodicC1HolderHalf)
    {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ radius) :
    ‖contourCauchyOperatorCLM data (nearby.trans_lt radius_small)‖ ≤ contourCauchyUniformOperatorConstant radius := by
  have circle_near : ‖standardCircleBanach - standardCircleBanach‖ ≤ radius := by simpa using radius_nonneg
  have difference_bound := contourCauchyOperatorCLM_parameter_norm_bound data standardCircleBanach
    radius_nonneg radius_small nearby circle_near
  have triangle := norm_add_le
    (contourCauchyOperatorCLM data (nearby.trans_lt radius_small) -
      contourCauchyOperatorCLM standardCircleBanach standardCircleBanach_small)
    (contourCauchyOperatorCLM standardCircleBanach standardCircleBanach_small)
  rw [sub_add_cancel (contourCauchyOperatorCLM data (nearby.trans_lt radius_small))
    (contourCauchyOperatorCLM standardCircleBanach standardCircleBanach_small)] at triangle
  have constant_nonneg := contourCauchyParameterOperatorConstant_nonneg radius_nonneg radius_small
  exact triangle.trans (add_le_add_right (difference_bound.trans
    (mul_le_mul_of_nonneg_left nearby constant_nonneg)) _)

end EulerNonuniqueness.Paper
