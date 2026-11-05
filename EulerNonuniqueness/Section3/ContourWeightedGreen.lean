import EulerNonuniqueness.Section3.ContourScalarGreen

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem contourPlaneTrace_smul_product (scalarDerivative : ℂ →L[ℝ] ℝ)
    (fieldDerivative : ℂ →L[ℝ] ℂ) (value : ℝ) (fieldValue : ℂ) :
    contourPlaneTrace (scalarDerivative.smulRight fieldValue + value • fieldDerivative) =
      scalarDerivative fieldValue + value * contourPlaneTrace fieldDerivative := by
  rw [realLinear_scalar_expansion scalarDerivative fieldValue]
  simp only [contourPlaneTrace, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add]
  ring

theorem integral_nearCircleInterior_directional_field
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (function : ℂ → ℝ) (scalarDerivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_continuous : Continuous function) (scalarDerivative_continuous : Continuous scalarDerivative)
    (function_derivative : ∀ position, HasFDerivAt function (scalarDerivative position) position)
    (field : ℂ → ℂ) (fieldDerivative : ℂ → ℂ →L[ℝ] ℂ)
    (field_continuous : Continuous field) (fieldDerivative_continuous : Continuous fieldDerivative)
    (field_derivative : ∀ position, HasFDerivAt field (fieldDerivative position) position)
    (divergence_zero : ∀ position, contourPlaneTrace (fieldDerivative position) = 0) :
    (∫ position in nearCircleInterior data small, scalarDerivative position (field position)) =
      ∫ label in (-Real.pi)..Real.pi, function (data.val.1 label) *
        contourAreaPair (field (data.val.1 label)) (data.val.2.val.1 label) := by
  let productDerivative : ℂ → ℂ →L[ℝ] ℂ := fun position =>
    (scalarDerivative position).smulRight (field position) + function position • fieldDerivative position
  have productDerivative_continuous : Continuous productDerivative := by
    apply Continuous.add
    · exact Continuous.clm_apply
        ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ).continuous.comp scalarDerivative_continuous) field_continuous
    · exact function_continuous.smul fieldDerivative_continuous
  have green := integral_nearCircleInterior_divergence data small
    (fun position => function position • field position) productDerivative
    (function_continuous.smul field_continuous) productDerivative_continuous
    (fun position => by
      simpa only [productDerivative, add_comm] using
        (function_derivative position).smul (field_derivative position))
  have trace_identity (position : ℂ) : contourPlaneTrace (productDerivative position) =
      scalarDerivative position (field position) := by
    dsimp only [productDerivative]
    rw [contourPlaneTrace_smul_product, divergence_zero position, mul_zero, add_zero]
  simp_rw [trace_identity] at green
  rw [green]
  apply intervalIntegral.integral_congr
  intro label _
  simp only [contourAreaPair_coordinates, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add]
  ring

end

end EulerNonuniqueness.Paper
