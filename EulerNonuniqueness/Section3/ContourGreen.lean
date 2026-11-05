import EulerNonuniqueness.Section3.ContourPlaneAlgebra
import EulerNonuniqueness.Section3.CompactParameterDifferentiation
import EulerNonuniqueness.Section3.MaterialPolarIntegration

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem contourGreen_radial_identity (linear : ℂ →L[ℝ] ℂ)
    (field position tangent : ℂ) (scale : ℝ) :
    contourAreaPair field tangent + scale * contourAreaPair (linear position) tangent -
      (contourAreaPair (linear (scale • tangent)) position + contourAreaPair field tangent) =
    scale * contourAreaPair position tangent * contourPlaneTrace linear := by
  rw [map_smul, contourAreaPair_coordinates, contourAreaPair_coordinates,
    contourAreaPair_coordinates, contourAreaPair_coordinates]
  have trace_identity := contourAreaPair_linear_trace linear position tangent
  rw [contourAreaPair_coordinates, contourAreaPair_coordinates, contourAreaPair_coordinates] at trace_identity
  simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, zero_add]
  linear_combination scale * trace_identity

theorem hasDerivAt_radialGreen_scale (field : ℂ → ℂ) (derivative : ℂ → ℂ →L[ℝ] ℂ)
    (field_derivative : ∀ position, HasFDerivAt field (derivative position) position)
    (position tangent : ℂ) (scale : ℝ) :
    HasDerivAt (fun parameter : ℝ => parameter * contourAreaPair (field (parameter • position)) tangent)
      (contourAreaPair (field (scale • position)) tangent +
        scale * contourAreaPair (derivative (scale • position) position) tangent) scale := by
  have radial_derivative : HasDerivAt (fun parameter : ℝ => parameter • position) position scale := by
    simpa using (hasDerivAt_id scale).smul_const position
  have determinant_derivative := hasDerivAt_contourAreaPair
    ((field_derivative _).comp_hasDerivAt scale radial_derivative) (hasDerivAt_const scale tangent)
  convert (hasDerivAt_id scale).mul determinant_derivative using 1 <;>
    simp [contourAreaPair, mul_zero]

theorem hasDerivAt_radialGreen_label (field : ℂ → ℂ) (derivative : ℂ → ℂ →L[ℝ] ℂ)
    (field_derivative : ∀ position, HasFDerivAt field (derivative position) position)
    {curve : ℝ → ℂ} {tangent : ℂ} {label : ℝ}
    (curve_derivative : HasDerivAt curve tangent label) (scale : ℝ) :
    HasDerivAt (fun parameter => contourAreaPair (field (scale • curve parameter)) (curve parameter))
      (contourAreaPair (derivative (scale • curve label) (scale • tangent)) (curve label) +
        contourAreaPair (field (scale • curve label)) tangent) label := by
  exact hasDerivAt_contourAreaPair
    ((field_derivative _).comp_hasDerivAt label (curve_derivative.const_smul scale)) curve_derivative

theorem integral_contourGreen_radial
    (field : ℂ → ℂ) (derivative : ℂ → ℂ →L[ℝ] ℂ)
    (field_continuous : Continuous field) (derivative_continuous : Continuous derivative)
    (field_derivative : ∀ position, HasFDerivAt field (derivative position) position)
    (curve tangent : ℝ → ℂ) (curve_continuous : Continuous curve)
    (tangent_continuous : Continuous tangent)
    (curve_derivative : ∀ label, HasDerivAt curve (tangent label) label)
    (lower upper : ℝ) (closed : curve upper = curve lower) :
    (∫ label in lower..upper, contourAreaPair (curve label) (tangent label) *
      ∫ scale in (0 : ℝ)..1, scale * contourPlaneTrace (derivative (scale • curve label))) =
    ∫ label in lower..upper, contourAreaPair (field (curve label)) (tangent label) := by
  let primitive : ℝ → ℝ → ℝ := fun label scale =>
    contourAreaPair (field (scale • curve label)) (curve label)
  let labelDerivative : ℝ → ℝ → ℝ := fun label scale =>
    contourAreaPair (derivative (scale • curve label) (scale • tangent label)) (curve label) +
      contourAreaPair (field (scale • curve label)) (tangent label)
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
    exact hasDerivAt_radialGreen_label field derivative field_derivative (curve_derivative parameter) scale
  have integrated_derivative_continuous :
      Continuous (fun label => ∫ scale in (0 : ℝ)..1, labelDerivative label scale) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
      labelDerivative_continuous continuous_const
  have derivative_integral_zero :
      (∫ label in lower..upper, ∫ scale in (0 : ℝ)..1, labelDerivative label scale) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun label _ => primitive_derivative label)
      (integrated_derivative_continuous.intervalIntegrable lower upper)]
    simp only [primitive, closed, sub_self]
  have radial_identity (label : ℝ) :
      contourAreaPair (curve label) (tangent label) *
        (∫ scale in (0 : ℝ)..1, scale * contourPlaneTrace (derivative (scale • curve label))) =
      contourAreaPair (field (curve label)) (tangent label) -
        ∫ scale in (0 : ℝ)..1, labelDerivative label scale := by
    let radialDerivative : ℝ → ℝ := fun scale =>
      contourAreaPair (field (scale • curve label)) (tangent label) +
        scale * contourAreaPair (derivative (scale • curve label) (curve label)) (tangent label)
    have radial_continuous : Continuous radialDerivative := by
      dsimp [radialDerivative, contourAreaPair]
      fun_prop
    have radial_integral : (∫ scale in (0 : ℝ)..1, radialDerivative scale) =
        contourAreaPair (field (curve label)) (tangent label) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun scale _ => hasDerivAt_radialGreen_scale field derivative field_derivative
          (curve label) (tangent label) scale)
        (radial_continuous.intervalIntegrable 0 1)]
      simp
    have label_slice_continuous : Continuous (labelDerivative label) :=
      labelDerivative_continuous.comp (continuous_const.prodMk continuous_id)
    rw [← radial_integral, ← intervalIntegral.integral_sub
      (radial_continuous.intervalIntegrable 0 1)
      (label_slice_continuous.intervalIntegrable 0 1),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro scale _
    dsimp only [radialDerivative, labelDerivative]
    simpa only [mul_left_comm, mul_assoc] using
      (contourGreen_radial_identity (derivative (scale • curve label))
        (field (scale • curve label)) (curve label) (tangent label) scale).symm
  have boundary_continuous : Continuous (fun label => contourAreaPair (field (curve label)) (tangent label)) := by
    unfold contourAreaPair
    fun_prop
  simp_rw [radial_identity]
  rw [intervalIntegral.integral_sub (boundary_continuous.intervalIntegrable lower upper)
    (integrated_derivative_continuous.intervalIntegrable lower upper), derivative_integral_zero, sub_zero]

theorem integral_nearCircleInterior_divergence
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (field : ℂ → ℂ) (derivative : ℂ → ℂ →L[ℝ] ℂ)
    (field_continuous : Continuous field) (derivative_continuous : Continuous derivative)
    (field_derivative : ∀ position, HasFDerivAt field (derivative position) position) :
    (∫ position in nearCircleInterior data small, contourPlaneTrace (derivative position)) =
      ∫ label in (-Real.pi)..Real.pi,
        contourAreaPair (field (data.val.1 label)) (data.val.2.val.1 label) := by
  have trace_continuous : Continuous (fun position => contourPlaneTrace (derivative position)) := by
    unfold contourPlaneTrace
    fun_prop
  rw [integral_nearCircleInterior_radial_flux data small _ trace_continuous]
  change (∫ label in (-Real.pi)..Real.pi,
    contourAreaPair (data.val.1 label) (data.val.2.val.1 label) *
      ∫ scale in (0 : ℝ)..1, scale * contourPlaneTrace (derivative (scale • data.val.1 label))) = _
  apply integral_contourGreen_radial field derivative field_continuous derivative_continuous
    field_derivative data.val.1 data.val.2.val.1 data.val.1.continuous data.val.2.val.1.continuous
    (PeriodicC1HolderHalf.hasDerivAt data) (-Real.pi) Real.pi
  have periodic := data.property.2 (-Real.pi)
  convert periodic using 1 <;> congr 1 <;> ring

end

end EulerNonuniqueness.Paper
