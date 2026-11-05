import EulerNonuniqueness.Section6.PatchCentroidLaw

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem domain_complex_integral_hasDerivAt (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count)
    (function : ℂ → ℂ) (derivative : ℂ → ℂ →L[ℝ] ℂ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ position, HasFDerivAt function (derivative position) position)
    (velocityIntegrable : IntegrableOn
      (fun position => derivative position (biotSavart (flow.vorticity time) position))
      (flow.domain time index)) :
    HasDerivAt (fun parameter => ∫ position in flow.domain parameter index, function position)
      (∫ position in flow.domain time index,
        derivative position (biotSavart (flow.vorticity time) position)) time := by
  have realDerivative := flow.domain_integral_hasDerivAt inside index
    (fun position => (function position).re) (fun position => Complex.reCLM.comp (derivative position))
    (Complex.continuous_re.comp functionContinuous) (continuous_const.clm_comp derivativeContinuous)
    (fun position => Complex.reCLM.hasFDerivAt.comp position (functionDerivative position))
  have imaginaryDerivative := flow.domain_integral_hasDerivAt inside index
    (fun position => (function position).im) (fun position => Complex.imCLM.comp (derivative position))
    (Complex.continuous_im.comp functionContinuous) (continuous_const.clm_comp derivativeContinuous)
    (fun position => Complex.imCLM.hasFDerivAt.comp position (functionDerivative position))
  have functionIntegral (parameter : ℝ) :
      ((∫ position in flow.domain parameter index, (function position).re : ℝ) : ℂ) +
        (∫ position in flow.domain parameter index, (function position).im : ℝ) * Complex.I =
      ∫ position in flow.domain parameter index, function position := by
    simpa only [integral_ofReal] using integral_coe_re_add_coe_im
      ((functionContinuous.continuousOn.integrableOn_compact
        (flow.domain_isBounded parameter index).isCompact_closure).mono_set subset_closure)
  have velocityIntegral :
      ((∫ position in flow.domain time index,
          (derivative position (biotSavart (flow.vorticity time) position)).re : ℝ) : ℂ) +
        (∫ position in flow.domain time index,
          (derivative position (biotSavart (flow.vorticity time) position)).im : ℝ) * Complex.I =
      ∫ position in flow.domain time index,
        derivative position (biotSavart (flow.vorticity time) position) := by
    simpa only [integral_ofReal] using integral_coe_re_add_coe_im velocityIntegrable
  have combined := realDerivative.ofReal_comp.add (imaginaryDerivative.ofReal_comp.mul_const Complex.I)
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply] at combined
  simpa only [functionIntegral, velocityIntegral] using combined

theorem domain_complex_second_moment_hasDerivAt (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    HasDerivAt (fun parameter => ∫ position in flow.domain parameter index, position ^ 2)
      (∫ position in flow.domain time index,
        2 * position * biotSavart (flow.vorticity time) position) time := by
  let derivative := fun position : ℂ =>
    (2 * position) • (ContinuousLinearMap.id ℝ ℂ)
  have derivativeContinuous : Continuous derivative :=
    (continuous_const.mul continuous_id).smul continuous_const
  have functionDerivative (position : ℂ) :
      HasFDerivAt (fun position : ℂ => position ^ 2) (derivative position) position := by
    convert ((hasDerivAt_pow 2 position).hasFDerivAt.restrictScalars ℝ) using 1
    ext direction
    simp [derivative, ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  obtain ⟨radius, _, radiusBound⟩ := (flow.domain_isBounded time index).exists_pos_norm_le
  have velocityIntegrable : IntegrableOn
      (fun position : ℂ => 2 * position * biotSavart (flow.vorticity time) position)
      (flow.domain time index) := by
    apply (flow.domain_velocity_integrable time index).bdd_mul'
      (((continuous_const.mul continuous_id : Continuous (fun position : ℂ => 2 * position))).aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem (flow.domain_isOpen time index).measurableSet] with position member
    simpa only [norm_mul, Complex.norm_ofNat] using mul_le_mul_of_nonneg_left
      (radiusBound position member) (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [derivative, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] using
    flow.domain_complex_integral_hasDerivAt inside index (fun position => position ^ 2) derivative
      (continuous_id.pow 2) derivativeContinuous functionDerivative velocityIntegrable

theorem subfamily_complex_second_moment_hasDerivAt (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (indices : Finset (Fin count)) :
    HasDerivAt (fun parameter => ∑ index ∈ indices, configuration.density index •
        (∫ position in flow.domain parameter index, position ^ 2))
      (∑ index ∈ indices, configuration.density index •
        (∫ position in flow.domain time index,
          2 * position * biotSavart (flow.vorticity time) position)) time := by
  exact HasDerivAt.sum fun index _ =>
    (flow.domain_complex_second_moment_hasDerivAt inside index).const_smul _

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
