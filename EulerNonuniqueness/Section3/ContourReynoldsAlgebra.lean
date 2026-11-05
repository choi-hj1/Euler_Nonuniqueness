import EulerNonuniqueness.Section3.ContourGreen

namespace EulerNonuniqueness.Paper

noncomputable section

theorem contourReynolds_pointwise_identity (linear : ℂ →L[ℝ] ℝ)
    (value scale : ℝ) (position tangent velocity mixed : ℂ) :
    scale * (linear (scale • velocity) * contourAreaPair position tangent +
        value * (contourAreaPair velocity tangent + contourAreaPair position mixed)) -
      scale * (linear (scale • tangent) * contourAreaPair position velocity +
        value * (contourAreaPair tangent velocity + contourAreaPair position mixed)) =
    (2 * scale * value + scale ^ 2 * linear position) * contourAreaPair velocity tangent := by
  simp only [map_smul, smul_eq_mul]
  have scalar_identity := contourAreaPair_scalar_identity linear position tangent velocity
  have antisymmetry := contourAreaPair_swap tangent velocity
  linear_combination scale ^ 2 * scalar_identity - scale * value * antisymmetry

theorem hasDerivAt_contourReynolds_time
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position)
    {curve tangent : ℝ → ℂ} {velocity mixed : ℂ} {time : ℝ}
    (curve_derivative : HasDerivAt curve velocity time)
    (tangent_derivative : HasDerivAt tangent mixed time) (scale : ℝ) :
    HasDerivAt (fun parameter => scale * function (scale • curve parameter) *
      contourAreaPair (curve parameter) (tangent parameter))
      (scale * (derivative (scale • curve time) (scale • velocity) * contourAreaPair (curve time) (tangent time) +
        function (scale • curve time) * (contourAreaPair velocity (tangent time) +
          contourAreaPair (curve time) mixed))) time := by
  have scalar_derivative := (function_derivative _).comp_hasDerivAt time (curve_derivative.const_smul scale)
  have area_derivative := hasDerivAt_contourAreaPair curve_derivative tangent_derivative
  convert (scalar_derivative.const_mul scale).mul area_derivative using 1 <;>
    simp only [Function.comp_apply] <;> ring

theorem hasDerivAt_contourReynolds_label
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position)
    {curve velocity : ℝ → ℂ} {tangent mixed : ℂ} {label : ℝ}
    (curve_derivative : HasDerivAt curve tangent label)
    (velocity_derivative : HasDerivAt velocity mixed label) (scale : ℝ) :
    HasDerivAt (fun parameter => scale * function (scale • curve parameter) *
      contourAreaPair (curve parameter) (velocity parameter))
      (scale * (derivative (scale • curve label) (scale • tangent) * contourAreaPair (curve label) (velocity label) +
        function (scale • curve label) * (contourAreaPair tangent (velocity label) +
          contourAreaPair (curve label) mixed))) label := by
  exact hasDerivAt_contourReynolds_time function derivative function_derivative curve_derivative velocity_derivative scale

theorem hasDerivAt_contourReynolds_radial
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position)
    (position tangent velocity : ℂ) (scale : ℝ) :
    HasDerivAt (fun parameter : ℝ => parameter ^ 2 * function (parameter • position) *
      contourAreaPair velocity tangent)
      ((2 * scale * function (scale • position) + scale ^ 2 * derivative (scale • position) position) *
        contourAreaPair velocity tangent) scale := by
  have radial_derivative : HasDerivAt (fun parameter : ℝ => parameter • position) position scale := by
    simpa using (hasDerivAt_id scale).smul_const position
  have scalar_derivative := (function_derivative _).comp_hasDerivAt scale radial_derivative
  convert (((hasDerivAt_id scale).pow 2).mul scalar_derivative).mul_const
    (contourAreaPair velocity tangent) using 1 <;> simp <;> ring

end

end EulerNonuniqueness.Paper
