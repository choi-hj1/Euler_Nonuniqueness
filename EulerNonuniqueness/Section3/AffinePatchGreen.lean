import EulerNonuniqueness.Section3.AffinePatchDomain
import EulerNonuniqueness.Section3.ContourWeightedGreen

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem integral_affinePatchDomain_divergence
    (center : ℂ) {radius : ℝ} (positive : 0 < radius) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (field : ℂ → ℂ) (derivative : ℂ → ℂ →L[ℝ] ℂ)
    (field_continuous : Continuous field) (derivative_continuous : Continuous derivative)
    (field_derivative : ∀ position, HasFDerivAt field (derivative position) position) :
    (∫ position in affinePatchDomain center radius data small, contourPlaneTrace (derivative position)) =
      ∫ label in (-Real.pi)..Real.pi,
        contourAreaPair (field (center + radius • data.val.1 label)) (radius • data.val.2.val.1 label) := by
  let affine : ℂ → ℂ := fun position => center + radius • position
  have affine_continuous : Continuous affine := continuous_const.add (continuous_const.smul continuous_id)
  have affine_derivative (position : ℂ) : HasFDerivAt affine (radius • ContinuousLinearMap.id ℝ ℂ) position := by
    simpa only [zero_add] using (hasFDerivAt_const (𝕜 := ℝ) center position).add
      ((hasFDerivAt_id (𝕜 := ℝ) position).const_smul radius)
  let pulledDerivative : ℂ → ℂ →L[ℝ] ℂ := fun position =>
    (derivative (affine position)).comp (radius • ContinuousLinearMap.id ℝ ℂ)
  have pulledDerivative_continuous : Continuous pulledDerivative :=
    (derivative_continuous.comp affine_continuous).clm_comp continuous_const
  have green := integral_nearCircleInterior_divergence data small (field ∘ affine) pulledDerivative
    (field_continuous.comp affine_continuous) pulledDerivative_continuous
    (fun position => (field_derivative (affine position)).comp position (affine_derivative position))
  have trace_identity (position : ℂ) : contourPlaneTrace (pulledDerivative position) =
      radius * contourPlaneTrace (derivative (affine position)) := by
    simp only [pulledDerivative, contourPlaneTrace, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_smul]
    simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, zero_add]
    ring
  simp_rw [trace_identity] at green
  rw [integral_const_mul] at green
  rw [integral_affinePatchDomain center positive data small]
  change radius ^ 2 * (∫ position in nearCircleInterior data small,
    contourPlaneTrace (derivative (affine position))) = _
  calc
    _ = radius * (radius * ∫ position in nearCircleInterior data small,
        contourPlaneTrace (derivative (affine position))) := by ring
    _ = radius * (∫ label in (-Real.pi)..Real.pi,
        contourAreaPair (field (affine (data.val.1 label))) (data.val.2.val.1 label)) := by
      simpa only [Function.comp_apply] using congrArg (fun value : ℝ => radius * value) green
    _ = _ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro label _
      dsimp only [Function.comp_apply, affine]
      simp only [contourAreaPair_coordinates, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add]
      ring

theorem integral_affinePatchDomain_directional_field
    (center : ℂ) {radius : ℝ} (positive : 0 < radius) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (function : ℂ → ℝ) (scalarDerivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_continuous : Continuous function) (scalarDerivative_continuous : Continuous scalarDerivative)
    (function_derivative : ∀ position, HasFDerivAt function (scalarDerivative position) position)
    (field : ℂ → ℂ) (fieldDerivative : ℂ → ℂ →L[ℝ] ℂ)
    (field_continuous : Continuous field) (fieldDerivative_continuous : Continuous fieldDerivative)
    (field_derivative : ∀ position, HasFDerivAt field (fieldDerivative position) position)
    (divergence_zero : ∀ position, contourPlaneTrace (fieldDerivative position) = 0) :
    (∫ position in affinePatchDomain center radius data small, scalarDerivative position (field position)) =
      ∫ label in (-Real.pi)..Real.pi, function (center + radius • data.val.1 label) *
        contourAreaPair (field (center + radius • data.val.1 label)) (radius • data.val.2.val.1 label) := by
  let productDerivative : ℂ → ℂ →L[ℝ] ℂ := fun position =>
    (scalarDerivative position).smulRight (field position) + function position • fieldDerivative position
  have productDerivative_continuous : Continuous productDerivative := by
    apply Continuous.add
    · exact Continuous.clm_apply
        ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ).continuous.comp scalarDerivative_continuous) field_continuous
    · exact function_continuous.smul fieldDerivative_continuous
  have green := integral_affinePatchDomain_divergence center positive data small
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

theorem affinePatchDomain_integrable_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (center : ℂ) {radius : ℝ} (positive : 0 < radius) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (function : ℂ → E)
    (function_continuous : Continuous function) :
    IntegrableOn function (affinePatchDomain center radius data small) := by
  have compact : IsCompact (closure (affinePatchDomain center radius data small)) :=
    (affinePatchDomain_isBounded center positive data small).isCompact_closure
  exact (function_continuous.continuousOn.integrableOn_compact compact).mono_set subset_closure

end

end EulerNonuniqueness.Paper
