import EulerNonuniqueness.Section3.ContourCauchyConstant

open MeasureTheory Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem contourCauchy_near_circle_principal_value_at {curve tangent : ℝ → ℂ}
    {holder difference : ℝ} (holder_nonneg : 0 ≤ holder) (difference_nonneg : 0 ≤ difference)
    (close : difference < 2 / Real.pi)
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (derivative : ∀ source : ℝ, HasDerivAt curve (tangent source) source)
    (holder_bound : ∀ first second : ℝ, ‖tangent first - tangent second‖ ≤ holder * Real.sqrt |first - second|)
    (derivative_difference : ∀ source : ℝ, ‖tangent source - standardCircleTangent source‖ ≤ difference)
    (periodic : Function.Periodic curve (2 * Real.pi)) (label : ℝ) :
    Tendsto (fun cutoff : ℝ =>
      (∫ source in (label - Real.pi)..(label - cutoff), contourCauchyKernel curve tangent label source) +
        ∫ source in (label + cutoff)..(label + Real.pi), contourCauchyKernel curve tangent label source)
      (𝓝[>] 0) (𝓝 (-(Real.pi : ℂ) * Complex.I)) := by
  let rotation := (standardCircle label)⁻¹
  let rotatedCurve := fun source => rotation * curve (source + label)
  let rotatedTangent := fun source => rotation * tangent (source + label)
  have rotation_norm : ‖rotation‖ = 1 := by simp [rotation, norm_inv, standardCircle_norm]
  have rotation_ne : rotation ≠ 0 := norm_ne_zero_iff.mp (by rw [rotation_norm]; norm_num)
  have circle_ne : standardCircle label ≠ 0 := by simp [standardCircle, Complex.exp_ne_zero]
  have rotated_curve_continuous : Continuous rotatedCurve :=
    continuous_const.mul (curve_continuous.comp (continuous_id.add continuous_const))
  have rotated_tangent_continuous : Continuous rotatedTangent :=
    continuous_const.mul (tangent_continuous.comp (continuous_id.add continuous_const))
  have rotated_derivative : ∀ source : ℝ, HasDerivAt rotatedCurve (rotatedTangent source) source := by
    intro source
    have actual := ((derivative (source + label)).scomp source ((hasDerivAt_id source).add_const label)).const_mul rotation
    simpa only [Function.comp_apply, id_eq, one_smul, rotatedCurve, rotatedTangent] using actual
  have rotated_holder : ∀ first second : ℝ,
      ‖rotatedTangent first - rotatedTangent second‖ ≤ holder * Real.sqrt |first - second| := by
    intro first second
    change ‖rotation * tangent (first + label) - rotation * tangent (second + label)‖ ≤ _
    rw [← mul_sub, norm_mul, rotation_norm, one_mul]
    simpa only [add_sub_add_right_eq_sub] using holder_bound (first + label) (second + label)
  have reference_rotation : ∀ source : ℝ,
      rotation * standardCircleTangent (source + label) = standardCircleTangent source := by
    intro source
    simp only [rotation, standardCircleTangent, standardCircle_add]
    field_simp [circle_ne]
    ring
  have rotated_difference : ∀ source : ℝ,
      ‖rotatedTangent source - standardCircleTangent source‖ ≤ difference := by
    intro source
    have identity : rotatedTangent source - standardCircleTangent source =
        rotation * (tangent (source + label) - standardCircleTangent (source + label)) := by
      rw [mul_sub, reference_rotation]
    rw [identity, norm_mul, rotation_norm, one_mul]
    exact derivative_difference (source + label)
  have rotated_closed : rotatedCurve (-Real.pi) = rotatedCurve Real.pi := by
    apply congrArg (fun position => rotation * position)
    have actual := (periodic (-Real.pi + label)).symm
    convert actual using 1 <;> congr 1 <;> ring
  have limit := contourCauchy_near_circle_principal_value holder_nonneg difference_nonneg close
    rotated_curve_continuous rotated_tangent_continuous (fun source _ => rotated_derivative source)
    (fun first _ second _ => rotated_holder first second) (fun source _ => rotated_difference source) rotated_closed
  have kernel_identity : ∀ source : ℝ,
      contourCauchyKernel rotatedCurve rotatedTangent 0 source =
        contourCauchyKernel curve tangent label (source + label) := by
    intro source
    change rotation * tangent (source + label) /
      (rotation * curve (0 + label) - rotation * curve (source + label)) = _
    rw [zero_add, ← mul_sub, mul_div_mul_left _ _ rotation_ne]
    rfl
  simp_rw [kernel_identity] at limit
  apply limit.congr'
  apply Eventually.of_forall
  intro cutoff
  dsimp only
  rw [intervalIntegral.integral_comp_add_right (contourCauchyKernel curve tangent label),
    intervalIntegral.integral_comp_add_right (contourCauchyKernel curve tangent label)]
  congr 1 <;> congr 1 <;> ring

end EulerNonuniqueness.Paper
