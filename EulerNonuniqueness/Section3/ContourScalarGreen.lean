import EulerNonuniqueness.Section3.ContourGreen
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem integral_nearCircleInterior_directional_derivative
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position)
    (direction : ℂ) :
    (∫ position in nearCircleInterior data small, derivative position direction) =
      ∫ label in (-Real.pi)..Real.pi,
        function (data.val.1 label) * contourAreaPair direction (data.val.2.val.1 label) := by
  have vector_derivative_continuous : Continuous (fun position => (derivative position).smulRight direction) := by
    exact Continuous.clm_apply
      ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ).continuous.comp derivative_continuous) continuous_const
  have green := integral_nearCircleInterior_divergence data small
    (fun position => function position • direction) (fun position => (derivative position).smulRight direction)
    (function_continuous.smul continuous_const) vector_derivative_continuous
    (fun position => (function_derivative position).smul_const direction)
  have trace_identity (position : ℂ) :
      contourPlaneTrace ((derivative position).smulRight direction) = derivative position direction := by
    rw [realLinear_scalar_expansion]
    simp only [contourPlaneTrace, ContinuousLinearMap.smulRight_apply, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add]
    ring
  simp_rw [trace_identity] at green
  rw [green]
  apply intervalIntegral.integral_congr
  intro label _
  simp only [contourAreaPair_coordinates, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add]
  ring

theorem nearCircleInterior_integrable_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (function : ℂ → E) (function_continuous : Continuous function) :
    IntegrableOn function (nearCircleInterior data small) := by
  have compact : IsCompact (closure (nearCircleInterior data small)) :=
    (nearCircleInterior_isBounded data small).isCompact_closure
  exact (function_continuous.continuousOn.integrableOn_compact compact).mono_set subset_closure

theorem integral_nearCircleInterior_complex_gradient
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position) :
    (∫ position in nearCircleInterior data small,
      ((derivative position 1 : ℝ) : ℂ) + Complex.I * (derivative position Complex.I : ℝ)) =
    -Complex.I * (∫ label in (-Real.pi)..Real.pi,
      function (data.val.1 label) • data.val.2.val.1 label) := by
  have gradient_continuous : Continuous (fun position =>
      ((derivative position 1 : ℝ) : ℂ) + Complex.I * (derivative position Complex.I : ℝ)) := by
    fun_prop
  have gradient_integrable := nearCircleInterior_integrable_of_continuous data small _ gradient_continuous
  have boundary_integrable : IntervalIntegrable
      (fun label => function (data.val.1 label) • data.val.2.val.1 label) volume (-Real.pi) Real.pi := by
    exact ((function_continuous.comp data.val.1.continuous).smul data.val.2.val.1.continuous).intervalIntegrable _ _
  apply Complex.ext
  · change Complex.reCLM _ = _
    rw [← Complex.reCLM.integral_comp_comm gradient_integrable]
    change (∫ position in nearCircleInterior data small,
      (((derivative position 1 : ℝ) : ℂ) + Complex.I * (derivative position Complex.I : ℝ)).re) = _
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    rw [integral_nearCircleInterior_directional_derivative data small function derivative
      function_continuous derivative_continuous function_derivative 1]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      neg_zero, zero_mul, neg_mul, one_mul, zero_sub, neg_neg]
    change _ = Complex.imCLM (∫ label in (-Real.pi)..Real.pi,
      function (data.val.1 label) • data.val.2.val.1 label)
    rw [← Complex.imCLM.intervalIntegral_comp_comm boundary_integrable]
    change _ = ∫ label in (-Real.pi)..Real.pi, (function (data.val.1 label) • data.val.2.val.1 label).im
    apply intervalIntegral.integral_congr
    intro label _
    simp [contourAreaPair_coordinates, Complex.real_smul]
  · change Complex.imCLM _ = _
    rw [← Complex.imCLM.integral_comp_comm gradient_integrable]
    change (∫ position in nearCircleInterior data small,
      (((derivative position 1 : ℝ) : ℂ) + Complex.I * (derivative position Complex.I : ℝ)).im) = _
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_add]
    rw [integral_nearCircleInterior_directional_derivative data small function derivative
      function_continuous derivative_continuous function_derivative Complex.I]
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      neg_zero, zero_mul, neg_mul, one_mul, zero_add]
    change _ = -Complex.reCLM (∫ label in (-Real.pi)..Real.pi,
      function (data.val.1 label) • data.val.2.val.1 label)
    rw [← Complex.reCLM.intervalIntegral_comp_comm boundary_integrable, ← intervalIntegral.integral_neg]
    change _ = ∫ label in (-Real.pi)..Real.pi, -(function (data.val.1 label) • data.val.2.val.1 label).re
    apply intervalIntegral.integral_congr
    intro label _
    simp [contourAreaPair_coordinates, Complex.real_smul]

end

end EulerNonuniqueness.Paper
