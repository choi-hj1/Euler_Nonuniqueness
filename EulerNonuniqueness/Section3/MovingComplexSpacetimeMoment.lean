import EulerNonuniqueness.Section3.MovingMaterialPatchMoments

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

private theorem integrable_domain_derivative_velocity (path : MovingMaterialPatch) (time : ℝ)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℂ) (derivativeContinuous : Continuous derivative) :
    IntegrableOn (fun position => derivative (time, position) (0, biotSavart source position)) (path.domain time) := by
  let bound := (eLpNorm source (ENNReal.ofReal (4 : ℝ)) volume).toReal *
      (eLpNorm ((Metric.ball (0 : ℂ) 1).indicator biotSavartKernel)
        (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
      (∫ position, ‖source position‖) * (1 / (2 * Real.pi))
  have coefficientContinuous : Continuous (fun position => derivative (time, position)) :=
    derivativeContinuous.comp (continuous_const.prodMk continuous_id)
  have measurableVelocity : AEStronglyMeasurable (fun position => (0, biotSavart source position) : ℂ → ℝ × ℂ)
      (volume.restrict (path.domain time)) :=
    aestronglyMeasurable_const.prodMk ((aestronglyMeasurable_biotSavart sourceIntegrable.aestronglyMeasurable).restrict)
  have measurableIntegrand : AEStronglyMeasurable
      (fun position => derivative (time, position) (0, biotSavart source position)) (volume.restrict (path.domain time)) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((coefficientContinuous.aestronglyMeasurable.restrict).prodMk measurableVelocity)
  apply (path.integral_continuous_function time (coefficientContinuous.norm.mul
    (continuous_const : Continuous (fun _ : ℂ => bound)))).mono' measurableIntegrand
  exact Filter.Eventually.of_forall fun position =>
    ((derivative (time, position)).le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)] using
        norm_biotSavart_le_L1_L4 sourceIntegrable sourceMembership position) (norm_nonneg _))

theorem domain_complex_spacetime_integral_hasDerivAt (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ label, path.boundaryVelocity time label = biotSavart source (path.boundary time label))
    (function : ℝ × ℂ → ℂ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℂ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ point, HasFDerivAt function (derivative point) point) :
    HasDerivAt (fun parameter => ∫ position in path.domain parameter, function (parameter, position))
      ((∫ position in path.domain time, derivative (time, position) (1, 0)) +
        ∫ position in path.domain time, derivative (time, position) (0, biotSavart source position)) time := by
  have realDerivative := path.domain_spacetime_integral_hasDerivAt inside sourceIntegrable sourceMembership material
    (fun point => (function point).re) (fun point => Complex.reCLM.comp (derivative point))
    (Complex.continuous_re.comp functionContinuous) (continuous_const.clm_comp derivativeContinuous)
    (fun point => Complex.reCLM.hasFDerivAt.comp point (functionDerivative point))
  have imaginaryDerivative := path.domain_spacetime_integral_hasDerivAt inside sourceIntegrable sourceMembership material
    (fun point => (function point).im) (fun point => Complex.imCLM.comp (derivative point))
    (Complex.continuous_im.comp functionContinuous) (continuous_const.clm_comp derivativeContinuous)
    (fun point => Complex.imCLM.hasFDerivAt.comp point (functionDerivative point))
  have result := realDerivative.ofReal_comp.add (imaginaryDerivative.ofReal_comp.mul_const Complex.I)
  have functionIdentity : (fun parameter =>
      ((∫ position in path.domain parameter, (function (parameter, position)).re : ℝ) : ℂ) +
        (∫ position in path.domain parameter, (function (parameter, position)).im : ℝ) * Complex.I) =
      fun parameter => ∫ position in path.domain parameter, function (parameter, position) := by
    funext parameter
    exact setIntegral_re_add_im (path.integral_continuous_function parameter
      (functionContinuous.comp (continuous_const.prodMk continuous_id)))
  rw [functionIdentity] at result
  have timeIntegrable : IntegrableOn (fun position => derivative (time, position) (1, 0)) (path.domain time) := path.integral_continuous_function time
    ((derivativeContinuous.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const)
  have velocityIntegrable := integrable_domain_derivative_velocity path time sourceIntegrable sourceMembership
    derivative derivativeContinuous
  convert result using 1
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply, Complex.ofReal_add]
  rw [← setIntegral_re_add_im timeIntegrable, ← setIntegral_re_add_im velocityIntegrable]
  dsimp only [RCLike.re, RCLike.im, RCLike.I]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  let temporalReal : ℝ := ∫ position in path.domain time, (derivative (time, position) (1, 0)).re
  let temporalImaginary : ℝ := ∫ position in path.domain time, (derivative (time, position) (1, 0)).im
  let spatialReal : ℝ := ∫ position in path.domain time, (derivative (time, position) (0, biotSavart source position)).re
  let spatialImaginary : ℝ := ∫ position in path.domain time, (derivative (time, position) (0, biotSavart source position)).im
  change ((temporalReal : ℂ) + (temporalImaginary : ℂ) * Complex.I) +
    ((spatialReal : ℂ) + (spatialImaginary : ℂ) * Complex.I) =
      ((temporalReal : ℂ) + (spatialReal : ℂ)) +
        ((temporalImaginary : ℂ) + (spatialImaginary : ℂ)) * Complex.I
  ring

theorem domain_complex_material_integral_hasDerivAt (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ label, path.boundaryVelocity time label = biotSavart source (path.boundary time label))
    (function : ℝ × ℂ → ℂ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℂ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ point, HasFDerivAt function (derivative point) point) :
    HasDerivAt (fun parameter => ∫ position in path.domain parameter, function (parameter, position))
      (∫ position in path.domain time, derivative (time, position) (1, biotSavart source position)) time := by
  have actual := path.domain_complex_spacetime_integral_hasDerivAt inside sourceIntegrable sourceMembership material
    function derivative functionContinuous derivativeContinuous functionDerivative
  have timeIntegrable : IntegrableOn (fun position => derivative (time, position) (1, 0)) (path.domain time) :=
    path.integral_continuous_function time
      ((derivativeContinuous.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const)
  have velocityIntegrable := integrable_domain_derivative_velocity path time sourceIntegrable sourceMembership
    derivative derivativeContinuous
  rw [← integral_add timeIntegrable velocityIntegrable] at actual
  convert actual using 1
  apply setIntegral_congr_fun (path.domain_isOpen time).measurableSet
  intro position _
  change derivative (time, position) (1, biotSavart source position) =
    derivative (time, position) (1, 0) + derivative (time, position) (0, biotSavart source position)
  rw [← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

end EulerNonuniqueness.Paper.MovingMaterialPatch
