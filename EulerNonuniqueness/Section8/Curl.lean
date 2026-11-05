import EulerNonuniqueness.Section8.SpatialRegularity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem hasCompactSupport_radial_test {test : Plane → ℝ}
    (compact : HasCompactSupport test) (angle : ℝ) :
    HasCompactSupport (fun radius : ℝ =>
      test ((radius : ℂ) * (Real.cos angle + Real.sin angle * Complex.I))) := by
  obtain ⟨bound, _, supportBound⟩ := compact.isCompact.isBounded.exists_pos_norm_le
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -bound) (b := bound))
  intro radius nonzero
  have inSupport : (radius : ℂ) * (Real.cos angle + Real.sin angle * Complex.I) ∈
      tsupport test := subset_tsupport _ nonzero
  have boundAt := supportBound _ inSupport
  have normEq : ‖(radius : ℂ) * (Real.cos angle + Real.sin angle * Complex.I)‖ = |radius| := by
    simpa only [Complex.polarCoord_symm_apply] using
      Complex.norm_polarCoord_symm (radius, angle)
  rw [normEq] at boundAt
  exact abs_le.mp boundAt

theorem integral_radial_derivative {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) (angle : ℝ) :
    (∫ radius in Ioi (0 : ℝ),
      fderiv ℝ test ((radius : ℂ) * (Real.cos angle + Real.sin angle * Complex.I))
        (Real.cos angle + Real.sin angle * Complex.I)) = -test 0 := by
  have radialSmooth : ContDiff ℝ ∞ (fun radius : ℝ =>
      test ((radius : ℂ) * (Real.cos angle + Real.sin angle * Complex.I))) := by
    apply smooth.comp
    exact Complex.ofRealCLM.contDiff.mul contDiff_const
  have derivative : ∀ radius : ℝ,
      deriv (fun parameter : ℝ =>
        test ((parameter : ℂ) * (Real.cos angle + Real.sin angle * Complex.I))) radius =
      fderiv ℝ test ((radius : ℂ) * (Real.cos angle + Real.sin angle * Complex.I))
        (Real.cos angle + Real.sin angle * Complex.I) := by
    intro radius
    have linearDerivative : HasDerivAt
        (fun parameter : ℝ => (parameter : ℂ) *
          ((Real.cos angle : ℂ) + Real.sin angle * Complex.I))
        ((Real.cos angle : ℂ) + Real.sin angle * Complex.I) radius := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := radius)).mul_const
        ((Real.cos angle : ℂ) + Real.sin angle * Complex.I)
    simpa using ((smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt
      radius linearDerivative).deriv
  have integral := HasCompactSupport.integral_Ioi_deriv_eq
    (radialSmooth.of_le (by simp)) (hasCompactSupport_radial_test compact angle) 0
  simp only [derivative, Complex.ofReal_zero, zero_mul] at integral
  exact integral

theorem mul_I_polar_biotSavartKernel {radius angle : ℝ} (positive : 0 < radius) :
    radius • (Complex.I * biotSavartKernel (Complex.polarCoord.symm (radius, angle))) =
      (-1 / (2 * Real.pi)) • (Real.cos angle + Real.sin angle * Complex.I) := by
  rw [polar_biotSavartKernel]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_pow]
  have nonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  field_simp [nonzero]
  ring_nf
  simp only [Complex.I_sq]
  have cancel : (radius : ℂ) ^ 2 * (radius : ℂ)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ nonzero, one_pow]
  linear_combination
    (Complex.I * Complex.sin (angle : ℂ) * (Real.pi : ℂ)⁻¹ * (-1 / 2) +
      Complex.cos (angle : ℂ) * (Real.pi : ℂ)⁻¹ * (-1 / 2)) * cancel

theorem locallyIntegrable_mul_I_biotSavartKernel :
    LocallyIntegrable (fun position => Complex.I * biotSavartKernel position) volume := by
  intro position
  obtain ⟨neighborhood, near, integrable⟩ := locallyIntegrable_biotSavartKernel position
  exact ⟨neighborhood, near, integrable.const_mul Complex.I⟩

theorem integrable_fderiv_mul_I_biotSavartKernel {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun position => fderiv ℝ test position
      (Complex.I * biotSavartKernel position)) :=
  integrable_fderiv_apply_of_locallyIntegrable locallyIntegrable_mul_I_biotSavartKernel
    (smooth.of_le (by simp)) compact

theorem integral_fderiv_mul_I_biotSavartKernel {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    (∫ position, fderiv ℝ test position (Complex.I * biotSavartKernel position)) = test 0 := by
  let integrand := fun position => fderiv ℝ test position
    (Complex.I * biotSavartKernel position)
  have measurableIntegrand : Measurable integrand :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((smooth.continuous_fderiv (by simp)).measurable.prodMk
        (measurable_const.mul measurable_biotSavartKernel))
  have continuousPolar : Continuous (fun point : ℝ × ℝ => Complex.polarCoord.symm point) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have polarIntegrable : Integrable
      (fun point : ℝ × ℝ => point.1 • integrand (Complex.polarCoord.symm point))
      (volume.restrict polarCoord.target) := by
    refine ⟨(measurable_fst.smul (measurableIntegrand.comp
      continuousPolar.measurable)).aestronglyMeasurable.restrict, ?_⟩
    exact (hasFiniteIntegral_polar_iff integrand).mpr
      (integrable_fderiv_mul_I_biotSavartKernel smooth compact).hasFiniteIntegral
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict] at polarIntegrable
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ polarIntegrable,
    integral_integral_swap polarIntegrable]
  have radialIntegral : ∀ angle : ℝ,
      (∫ radius in Ioi (0 : ℝ), radius • integrand (Complex.polarCoord.symm (radius, angle))) =
        (-1 / (2 * Real.pi)) * (-test 0) := by
    intro angle
    calc
      _ = ∫ radius in Ioi (0 : ℝ), (-1 / (2 * Real.pi)) *
          fderiv ℝ test ((radius : ℂ) * (Real.cos angle + Real.sin angle * Complex.I))
            (Real.cos angle + Real.sin angle * Complex.I) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro radius positive
        dsimp only [integrand]
        rw [← map_smul, mul_I_polar_biotSavartKernel positive, map_smul]
        simp only [Complex.polarCoord_symm_apply, smul_eq_mul]
      _ = _ := by rw [integral_const_mul, integral_radial_derivative smooth compact]
  change (∫ angle in Ioo (-Real.pi) Real.pi,
    ∫ radius in Ioi (0 : ℝ), radius • integrand (Complex.polarCoord.symm (radius, angle))) = _
  simp_rw [radialIntegral]
  simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), smul_eq_mul]
  field_simp
  ring

theorem integral_fderiv_shift_mul_I_biotSavartKernel {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) (source : Plane) :
    (∫ position, fderiv ℝ test position
      (Complex.I * biotSavartKernel (position - source))) = test source := by
  have shiftedSmooth : ContDiff ℝ ∞ (fun position => test (position + source)) :=
    smooth.comp (contDiff_id.add contDiff_const)
  have shiftedCompact : HasCompactSupport (fun position => test (position + source)) :=
    compact.comp_homeomorph (Homeomorph.addRight source)
  have identity := integral_fderiv_mul_I_biotSavartKernel shiftedSmooth shiftedCompact
  simp only [fderiv_comp_add_right, zero_add] at identity
  rw [← integral_add_right_eq_self (fun position => fderiv ℝ test position
    (Complex.I * biotSavartKernel (position - source))) source]
  simpa only [add_sub_cancel_right] using identity

theorem integrable_biotSavart_curl_test_integrand {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {test : Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun point : Plane × Plane => fderiv ℝ test point.1
      (Complex.I * (vorticity point.2 • biotSavartKernel (point.1 - point.2))))
      (volume.prod volume) := by
  have originalMeasurable : AEStronglyMeasurable
      (fun point : Plane × Plane => vorticity point.2 • biotSavartKernel (point.1 - point.2))
      (volume.prod volume) := integrable.aestronglyMeasurable.convolution_integrand
    (ContinuousLinearMap.lsmul ℝ ℝ) measurable_biotSavartKernel.aestronglyMeasurable
  apply (integrable_biotSavart_test_integrand_norm integrable supportBound (smooth.of_le (by simp)) compact).mono'
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((smooth.continuous_fderiv (by simp)).comp continuous_fst).aestronglyMeasurable.prodMk
        (aestronglyMeasurable_const.mul originalMeasurable))
  · filter_upwards [] with point
    simpa only [norm_mul, Complex.norm_I, one_mul] using
      (fderiv ℝ test point.1).le_opNorm
        (Complex.I * (vorticity point.2 • biotSavartKernel (point.1 - point.2)))

theorem curl_biotSavart_of_integrable_support {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {test : Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun position => fderiv ℝ test position
      (Complex.I * biotSavart vorticity position)) ∧
      (∫ position, fderiv ℝ test position (Complex.I * biotSavart vorticity position)) =
        ∫ position, vorticity position * test position := by
  have locallyIntegrable : LocallyIntegrable
      (fun position => Complex.I * biotSavart vorticity position) volume := by
    intro position
    obtain ⟨neighborhood, near, localIntegrable⟩ :=
      locallyIntegrable_biotSavart_of_integrable_support integrable supportBound position
    exact ⟨neighborhood, near, localIntegrable.const_mul Complex.I⟩
  refine ⟨integrable_fderiv_apply_of_locallyIntegrable locallyIntegrable (smooth.of_le (by simp)) compact, ?_⟩
  have equality : ∀ᵐ position ∂(volume : Measure Plane),
      fderiv ℝ test position (Complex.I * biotSavart vorticity position) =
        ∫ source, fderiv ℝ test position
          (Complex.I * (vorticity source • biotSavartKernel (position - source))) := by
    filter_upwards [biotSavartIntegrable_of_integrable_support integrable supportBound]
      with position convolutionIntegrable
    rw [biotSavart, ← integral_const_mul]
    exact ((fderiv ℝ test position).integral_comp_comm
      (convolutionIntegrable.const_mul Complex.I)).symm
  rw [integral_congr_ae equality, integral_integral_swap
    (integrable_biotSavart_curl_test_integrand integrable supportBound smooth compact)]
  apply integral_congr_ae
  filter_upwards [] with source
  simp_rw [mul_smul_comm, map_smul, smul_eq_mul]
  rw [integral_const_mul, integral_fderiv_shift_mul_I_biotSavartKernel smooth compact]

end EulerNonuniqueness
