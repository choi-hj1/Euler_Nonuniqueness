import EulerNonuniqueness.Section3.ContourDensityFarParameter

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

noncomputable def contourCauchyParameterHolderLocalConstant (radius : ℝ) : ℝ :=
  16 * contourKernelParameterSizeConstant radius + 2 * Real.sqrt 2 * contourKernelParameterSmoothConstant radius +
    contourKernelParameterSizeConstant radius * (4 * Real.sqrt Real.pi + 2)

set_option maxHeartbeats 2000000 in
theorem contourCauchyTransform_parameter_holder_local (first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius jump : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius)
    (jump_pos : 0 < jump) (jump_small : jump ≤ Real.pi / 8) :
    ‖(contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 0 -
        contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 0) -
      (contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 jump -
        contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 jump)‖ ≤
      contourCauchyParameterHolderLocalConstant radius * ‖first - second‖ * ‖density‖ * Real.sqrt jump := by
  let nearZero :=
    (∫ source in (-2 * jump)..(2 * jump), contourCauchyDensityRemainder first.val.1 first.val.2.val.1 density.val.1 0 source) -
    ∫ source in (-2 * jump)..(2 * jump), contourCauchyDensityRemainder second.val.1 second.val.2.val.1 density.val.1 0 source
  let nearJump :=
    (∫ source in (-2 * jump)..(2 * jump), contourCauchyDensityRemainder first.val.1 first.val.2.val.1 density.val.1 jump source) -
    ∫ source in (-2 * jump)..(2 * jump), contourCauchyDensityRemainder second.val.1 second.val.2.val.1 density.val.1 jump source
  let farLeft := ∫ source in (-Real.pi)..(-2 * jump), contourCauchyParameterFarIntegrand first second density jump source
  let farRight := ∫ source in (2 * jump)..Real.pi, contourCauchyParameterFarIntegrand first second density jump source
  let kernelFar :=
    ((∫ source in (-Real.pi)..(-2 * jump), contourCauchyKernel first.val.1 first.val.2.val.1 jump source) +
      ∫ source in (2 * jump)..Real.pi, contourCauchyKernel first.val.1 first.val.2.val.1 jump source) -
    ((∫ source in (-Real.pi)..(-2 * jump), contourCauchyKernel second.val.1 second.val.2.val.1 jump source) +
      ∫ source in (2 * jump)..Real.pi, contourCauchyKernel second.val.1 second.val.2.val.1 jump source)
  let densityTerm := (density.val.1 jump - density.val.1 0) * kernelFar
  have first_identity := banachContourCauchyTransform_difference_decomposition first density
    (first_near.trans_lt radius_small) jump_pos jump_small
  have second_identity := banachContourCauchyTransform_difference_decomposition second density
    (second_near.trans_lt radius_small) jump_pos jump_small
  have left_identity := contourCauchy_parameter_far_integral_difference first second density
    (first_near.trans_lt radius_small) (second_near.trans_lt radius_small) jump_pos jump_small
    (lower := -Real.pi) (upper := -2 * jump)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inl (by linarith))
  have right_identity := contourCauchy_parameter_far_integral_difference first second density
    (first_near.trans_lt radius_small) (second_near.trans_lt radius_small) jump_pos jump_small
    (lower := 2 * jump) (upper := Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inr (by linarith))
  have identity :
      (contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 0 -
        contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 0) -
      (contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 jump -
        contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 jump) =
      (nearZero - nearJump) + (farLeft + farRight) + densityTerm := by
    dsimp only [nearZero, nearJump, farLeft, farRight, densityTerm, kernelFar]
    linear_combination first_identity - second_identity + left_identity + right_identity
  have near_zero_bound : ‖nearZero‖ ≤ 8 * ‖density‖ * ‖first - second‖ *
      contourKernelParameterSizeConstant radius * Real.sqrt jump :=
    contourCauchyDensityRemainder_parameter_near_bound first second density radius_nonneg radius_small
      first_near second_near jump_pos jump_small ⟨le_rfl, jump_pos.le⟩
  have near_jump_bound : ‖nearJump‖ ≤ 8 * ‖density‖ * ‖first - second‖ *
      contourKernelParameterSizeConstant radius * Real.sqrt jump :=
    contourCauchyDensityRemainder_parameter_near_bound first second density radius_nonneg radius_small
      first_near second_near jump_pos jump_small ⟨jump_pos.le, le_rfl⟩
  have far_left_bound : ‖farLeft‖ ≤ (‖first - second‖ * contourKernelParameterSmoothConstant radius * ‖density‖) *
      Real.sqrt (2 * jump) := contourCauchyParameterFarIntegrand_integral_left_bound first second density
        radius_nonneg radius_small first_near second_near jump_pos jump_small
  have far_right_bound : ‖farRight‖ ≤ (‖first - second‖ * contourKernelParameterSmoothConstant radius * ‖density‖) *
      Real.sqrt (2 * jump) := contourCauchyParameterFarIntegrand_integral_right_bound first second density
        radius_nonneg radius_small first_near second_near jump_pos jump_small
  have kernel_far_bound : ‖kernelFar‖ ≤ ‖first - second‖ * contourKernelParameterSizeConstant radius *
      (4 * Real.sqrt Real.pi + 2) := contourCauchyKernel_parameter_far_integral_difference_bound first second
        radius_nonneg radius_small first_near second_near jump_pos jump_small
  have density_difference : ‖density.val.1 jump - density.val.1 0‖ ≤ ‖density‖ * Real.sqrt jump := by
    simpa only [sub_zero, abs_of_pos jump_pos] using PeriodicHolderHalf.holder_bound density jump 0
  have density_term_bound : ‖densityTerm‖ ≤ (‖density‖ * Real.sqrt jump) *
      (‖first - second‖ * contourKernelParameterSizeConstant radius * (4 * Real.sqrt Real.pi + 2)) := by
    change ‖(density.val.1 jump - density.val.1 0) * kernelFar‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul density_difference kernel_far_bound (norm_nonneg _) (by positivity)
  rw [identity]
  have norm_bound := norm_cauchy_decomposition_le nearZero nearJump farLeft farRight densityTerm 0
  simp only [sub_zero, norm_zero, add_zero] at norm_bound
  calc
    _ ≤ ‖nearZero‖ + ‖nearJump‖ + ‖farLeft‖ + ‖farRight‖ + ‖densityTerm‖ := norm_bound
    _ ≤ 2 * (8 * ‖density‖ * ‖first - second‖ * contourKernelParameterSizeConstant radius) * Real.sqrt jump +
        2 * (‖first - second‖ * contourKernelParameterSmoothConstant radius * ‖density‖) * Real.sqrt (2 * jump) +
        (‖density‖ * Real.sqrt jump) * (‖first - second‖ * contourKernelParameterSizeConstant radius *
          (4 * Real.sqrt Real.pi + 2)) := by linarith
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      unfold contourCauchyParameterHolderLocalConstant
      ring

end EulerNonuniqueness.Paper
