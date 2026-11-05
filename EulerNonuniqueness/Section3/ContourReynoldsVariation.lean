import EulerNonuniqueness.Section3.ContourReynoldsAlgebra

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

def contourReynoldsVariation (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (curve tangent velocity mixed : ℝ → ℂ) (label scale : ℝ) : ℝ :=
  scale * (derivative (scale • curve label) (scale • velocity label) * contourAreaPair (curve label) (tangent label) +
    function (scale • curve label) * (contourAreaPair (velocity label) (tangent label) +
      contourAreaPair (curve label) (mixed label)))

theorem integral_contourReynolds_variation
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position)
    (curve tangent velocity mixed : ℝ → ℂ)
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (velocity_continuous : Continuous velocity) (mixed_continuous : Continuous mixed)
    (curve_derivative : ∀ label, HasDerivAt curve (tangent label) label)
    (velocity_derivative : ∀ label, HasDerivAt velocity (mixed label) label)
    (lower upper : ℝ) (closed_curve : curve upper = curve lower)
    (closed_velocity : velocity upper = velocity lower) :
    (∫ label in lower..upper, ∫ scale in (0 : ℝ)..1,
      contourReynoldsVariation function derivative curve tangent velocity mixed label scale) =
      ∫ label in lower..upper,
        function (curve label) * contourAreaPair (velocity label) (tangent label) := by
  let primitive : ℝ → ℝ → ℝ := fun label scale =>
    scale * function (scale • curve label) * contourAreaPair (curve label) (velocity label)
  let labelDerivative : ℝ → ℝ → ℝ := fun label scale =>
    scale * (derivative (scale • curve label) (scale • tangent label) * contourAreaPair (curve label) (velocity label) +
      function (scale • curve label) * (contourAreaPair (tangent label) (velocity label) +
        contourAreaPair (curve label) (mixed label)))
  have primitive_continuous : Continuous (Function.uncurry primitive) := by
    dsimp [primitive, Function.uncurry, contourAreaPair]
    fun_prop
  have labelDerivative_continuous : Continuous (Function.uncurry labelDerivative) := by
    dsimp [labelDerivative, Function.uncurry, contourAreaPair]
    fun_prop
  have primitive_derivative (label : ℝ) :
      HasDerivAt (fun parameter => ∫ scale in (0 : ℝ)..1, primitive parameter scale)
        (∫ scale in (0 : ℝ)..1, labelDerivative label scale) label := by
    apply hasDerivAt_intervalIntegral_of_joint_continuous primitive labelDerivative label 0 1 1
      zero_lt_one primitive_continuous labelDerivative_continuous
    intro scale _ parameter _
    exact hasDerivAt_contourReynolds_label function derivative function_derivative
      (curve_derivative parameter) (velocity_derivative parameter) scale
  have integrated_derivative_continuous :
      Continuous (fun label => ∫ scale in (0 : ℝ)..1, labelDerivative label scale) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
      labelDerivative_continuous continuous_const
  have derivative_integral_zero :
      (∫ label in lower..upper, ∫ scale in (0 : ℝ)..1, labelDerivative label scale) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun label _ => primitive_derivative label)
      (integrated_derivative_continuous.intervalIntegrable lower upper)]
    simp only [primitive, closed_curve, closed_velocity, sub_self]
  have radial_identity (label : ℝ) :
      (∫ scale in (0 : ℝ)..1,
        contourReynoldsVariation function derivative curve tangent velocity mixed label scale) =
      function (curve label) * contourAreaPair (velocity label) (tangent label) +
        ∫ scale in (0 : ℝ)..1, labelDerivative label scale := by
    let radialDerivative : ℝ → ℝ := fun scale =>
      (2 * scale * function (scale • curve label) + scale ^ 2 * derivative (scale • curve label) (curve label)) *
        contourAreaPair (velocity label) (tangent label)
    have radial_continuous : Continuous radialDerivative := by
      dsimp [radialDerivative, contourAreaPair]
      fun_prop
    have radial_integral : (∫ scale in (0 : ℝ)..1, radialDerivative scale) =
        function (curve label) * contourAreaPair (velocity label) (tangent label) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun scale _ => hasDerivAt_contourReynolds_radial function derivative function_derivative
          (curve label) (tangent label) (velocity label) scale)
        (radial_continuous.intervalIntegrable 0 1)]
      simp
    have label_slice_continuous : Continuous (labelDerivative label) :=
      labelDerivative_continuous.comp (continuous_const.prodMk continuous_id)
    rw [← radial_integral, ← intervalIntegral.integral_add
      (radial_continuous.intervalIntegrable 0 1) (label_slice_continuous.intervalIntegrable 0 1)]
    apply intervalIntegral.integral_congr
    intro scale _
    dsimp only [contourReynoldsVariation, radialDerivative, labelDerivative]
    have identity := contourReynolds_pointwise_identity (derivative (scale • curve label))
      (function (scale • curve label)) scale (curve label) (tangent label) (velocity label) (mixed label)
    linarith
  have boundary_continuous : Continuous (fun label =>
      function (curve label) * contourAreaPair (velocity label) (tangent label)) := by
    unfold contourAreaPair
    fun_prop
  simp_rw [radial_identity]
  rw [intervalIntegral.integral_add (boundary_continuous.intervalIntegrable lower upper)
    (integrated_derivative_continuous.intervalIntegrable lower upper), derivative_integral_zero, add_zero]

end

end EulerNonuniqueness.Paper
