import EulerNonuniqueness.Section3.ContourAnalyticMoments
import EulerNonuniqueness.Section3.ContourScalarGreen

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem contourPolynomialMoment_one_eq_domain_integral (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    contourPolynomialMoment 1 data = ∫ position in nearCircleInterior data small, position := by
  let function : ℂ → ℝ := fun position => (position.re ^ 2 + position.im ^ 2) / 2
  let derivative : ℂ → ℂ →L[ℝ] ℝ := fun position =>
    position.re • Complex.reCLM + position.im • Complex.imCLM
  have function_continuous : Continuous function := by fun_prop
  have derivative_continuous : Continuous derivative := by fun_prop
  have function_derivative (position : ℂ) : HasFDerivAt function (derivative position) position := by
    have real_derivative := Complex.reCLM.hasFDerivAt (x := position)
    have imaginary_derivative := Complex.imCLM.hasFDerivAt (x := position)
    have result := ((real_derivative.mul real_derivative).add
      (imaginary_derivative.mul imaginary_derivative)).const_mul (1 / 2 : ℝ)
    have function_identity : (fun point : ℂ => (1 / 2 : ℝ) *
        (Complex.reCLM point * Complex.reCLM point + Complex.imCLM point * Complex.imCLM point)) = function := by
      funext point
      dsimp [function]
      ring
    rw [function_identity] at result
    convert result using 1
    ext direction
    simp only [derivative, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Complex.reCLM_apply, Complex.imCLM_apply]
    ring
  have gradient_identity (position : ℂ) :
      ((derivative position 1 : ℝ) : ℂ) + Complex.I * (derivative position Complex.I : ℝ) = position := by
    simp only [derivative, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Complex.reCLM_apply, Complex.imCLM_apply, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero, zero_add]
    rw [mul_comm Complex.I]
    exact Complex.re_add_im position
  have green := integral_nearCircleInterior_complex_gradient data small function derivative function_continuous
    derivative_continuous function_derivative
  simp_rw [gradient_identity] at green
  have integrand_identity : (fun label => function (data.val.1 label) • data.val.2.val.1 label) =
      fun label => (1 / 2 : ℂ) * (data.val.1 label * star (data.val.1 label) * data.val.2.val.1 label) := by
    funext label
    have scalar_identity (position : ℂ) : (function position : ℂ) = (1 / 2 : ℂ) * (position * star position) := by
      simp only [function, Complex.star_def, Complex.mul_conj, Complex.normSq_apply]
      push_cast
      ring
    rw [Complex.real_smul, scalar_identity]
    ring
  rw [integrand_identity, intervalIntegral.integral_const_mul] at green
  rw [contourPolynomialMoment_eq_integral]
  simp only [pow_one]
  rw [green]
  ring

end

end EulerNonuniqueness.Paper
