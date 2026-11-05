import EulerNonuniqueness.Section8.BiotSavart
import EulerNonuniqueness.General.PolarIntegration
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem integrable_fderiv_apply_of_locallyIntegrable {velocity : Velocity}
    (locallyIntegrable : LocallyIntegrable velocity volume) {test : Plane → ℝ}
    (smooth : ContDiff ℝ 1 test) (compact : HasCompactSupport test) :
    Integrable (fun position => fderiv ℝ test position (velocity position)) := by
  have continuousDerivative : Continuous (fderiv ℝ test) :=
    smooth.continuous_fderiv (by simp)
  have normLocallyIntegrable : LocallyIntegrable (fun position => ‖velocity position‖) volume := by
    intro position
    obtain ⟨neighborhood, near, integrable⟩ := locallyIntegrable position
    exact ⟨neighborhood, near, integrable.norm⟩
  have bound := normLocallyIntegrable.integrable_smul_right_of_hasCompactSupport
    continuousDerivative (compact.fderiv (𝕜 := ℝ))
  apply bound.norm.mono'
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (continuousDerivative.aestronglyMeasurable.prodMk locallyIntegrable.aestronglyMeasurable)
  · filter_upwards [] with position
    simpa [norm_smul, mul_comm] using
      (fderiv ℝ test position).le_opNorm (velocity position)

theorem hasDerivAt_circle (radius angle : ℝ) :
    HasDerivAt (fun parameter : ℝ =>
      (radius : ℂ) * (Real.cos parameter + Real.sin parameter * Complex.I))
      ((radius : ℂ) * (-Real.sin angle + Real.cos angle * Complex.I)) angle := by
  convert (hasDerivAt_const angle (radius : ℂ)).mul
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt angle (Real.hasDerivAt_cos angle)).add
      ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt angle
        (Real.hasDerivAt_sin angle)).mul_const Complex.I)) using 1
  simp

theorem integral_angular_derivative_eq_zero {test : Plane → ℝ}
    (smooth : ContDiff ℝ 1 test) (radius : ℝ) :
    (∫ angle in -Real.pi..Real.pi,
      fderiv ℝ test ((radius : ℂ) * (Real.cos angle + Real.sin angle * Complex.I))
        ((radius : ℂ) * (-Real.sin angle + Real.cos angle * Complex.I))) = 0 := by
  have differentiable := smooth.differentiable (by simp)
  have derivative : ∀ angle : ℝ, HasDerivAt
      (fun parameter : ℝ => test ((radius : ℂ) *
        (Real.cos parameter + Real.sin parameter * Complex.I)))
      (fderiv ℝ test ((radius : ℂ) * (Real.cos angle + Real.sin angle * Complex.I))
        ((radius : ℂ) * (-Real.sin angle + Real.cos angle * Complex.I))) angle := by
    intro angle
    exact (differentiable _).hasFDerivAt.comp_hasDerivAt angle (hasDerivAt_circle radius angle)
  have continuousDerivative : Continuous (fun angle : ℝ =>
      fderiv ℝ test ((radius : ℂ) * (Real.cos angle + Real.sin angle * Complex.I))
        ((radius : ℂ) * (-Real.sin angle + Real.cos angle * Complex.I))) := by
    apply Continuous.clm_apply
    · exact (smooth.continuous_fderiv (by simp)).comp (by fun_prop)
    · fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun angle _ => derivative angle) (continuousDerivative.intervalIntegrable _ _)]
  simp

theorem polar_biotSavartKernel (radius angle : ℝ) :
    biotSavartKernel (Complex.polarCoord.symm (radius, angle)) =
      (1 / (2 * Real.pi * radius ^ 2)) •
        ((radius : ℂ) * (-Real.sin angle + Real.cos angle * Complex.I)) := by
  rw [biotSavartKernel, Complex.norm_polarCoord_symm, sq_abs,
    Complex.polarCoord_symm_apply]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, div_eq_mul_inv]
  ring_nf
  simp only [Complex.I_sq, map_mul, map_inv₀, map_pow, Complex.ofReal_ofNat]
  push_cast
  ring

theorem integral_angular_biotSavartKernel_eq_zero {test : Plane → ℝ}
    (smooth : ContDiff ℝ 1 test) (radius : ℝ) :
    (∫ angle in Ioo (-Real.pi) Real.pi,
      radius * fderiv ℝ test (Complex.polarCoord.symm (radius, angle))
        (biotSavartKernel (Complex.polarCoord.symm (radius, angle)))) = 0 := by
  simp_rw [polar_biotSavartKernel, map_smul, smul_eq_mul]
  simp_rw [← mul_assoc]
  rw [integral_const_mul]
  have angular := integral_angular_derivative_eq_zero smooth radius
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo] at angular
  simp only [Complex.polarCoord_symm_apply, angular, mul_zero]

theorem integrable_fderiv_biotSavartKernel {test : Plane → ℝ}
    (smooth : ContDiff ℝ 1 test) (compact : HasCompactSupport test) :
    Integrable (fun position => fderiv ℝ test position (biotSavartKernel position)) :=
  integrable_fderiv_apply_of_locallyIntegrable locallyIntegrable_biotSavartKernel smooth compact

theorem integral_fderiv_biotSavartKernel_eq_zero {test : Plane → ℝ}
    (smooth : ContDiff ℝ 1 test) (compact : HasCompactSupport test) :
    (∫ position, fderiv ℝ test position (biotSavartKernel position)) = 0 := by
  let integrand := fun position => fderiv ℝ test position (biotSavartKernel position)
  have measurableIntegrand : Measurable integrand :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((smooth.continuous_fderiv (by simp)).measurable.prodMk measurable_biotSavartKernel)
  have continuousPolar : Continuous (fun point : ℝ × ℝ => Complex.polarCoord.symm point) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have polarIntegrable : Integrable
      (fun point : ℝ × ℝ => point.1 • integrand (Complex.polarCoord.symm point))
      (volume.restrict polarCoord.target) := by
    refine ⟨(measurable_fst.smul (measurableIntegrand.comp
      continuousPolar.measurable)).aestronglyMeasurable.restrict, ?_⟩
    exact (hasFiniteIntegral_polar_iff integrand).mpr
      (integrable_fderiv_biotSavartKernel smooth compact).hasFiniteIntegral
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict] at polarIntegrable
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [integral_prod _ polarIntegrable]
  have innerZero : ∀ radius : ℝ,
      (∫ angle in Ioo (-Real.pi) Real.pi,
        radius • integrand (Complex.polarCoord.symm (radius, angle))) = 0 := by
    intro radius
    exact integral_angular_biotSavartKernel_eq_zero smooth radius
  simp only [innerZero, integral_zero]

theorem integral_fderiv_shift_biotSavartKernel_eq_zero {test : Plane → ℝ}
    (smooth : ContDiff ℝ 1 test) (compact : HasCompactSupport test) (source : Plane) :
    (∫ position, fderiv ℝ test position (biotSavartKernel (position - source))) = 0 := by
  have shiftedSmooth : ContDiff ℝ 1 (fun position => test (position + source)) :=
    smooth.comp (contDiff_id.add contDiff_const)
  have shiftedCompact : HasCompactSupport (fun position => test (position + source)) :=
    compact.comp_homeomorph (Homeomorph.addRight source)
  have zero := integral_fderiv_biotSavartKernel_eq_zero shiftedSmooth shiftedCompact
  simp only [fderiv_comp_add_right] at zero
  rw [← integral_add_right_eq_self
    (fun position => fderiv ℝ test position (biotSavartKernel (position - source))) source]
  simpa only [add_sub_cancel_right] using zero

theorem integrable_biotSavart_test_integrand_norm {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {test : Plane → ℝ} (smooth : ContDiff ℝ 1 test) (compact : HasCompactSupport test) :
    Integrable (fun point : Plane × Plane =>
      ‖fderiv ℝ test point.1‖ * ‖vorticity point.2 • biotSavartKernel (point.1 - point.2)‖)
      (volume.prod volume) := by
  have continuousDerivative := smooth.continuous_fderiv (by simp)
  have compactDerivative := compact.fderiv (𝕜 := ℝ)
  obtain ⟨observationRadius, _, observationBound⟩ :=
    compactDerivative.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨bound, boundPositive, derivativeBound⟩ :=
    (compactDerivative.isCompact.image continuousDerivative).isBounded.exists_pos_norm_le
  let truncated := (Metric.ball 0 (observationRadius + radius + 1)).indicator biotSavartKernel
  have truncatedIntegrable : Integrable truncated :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_biotSavartKernel_ball _)
  have convolutionIntegrable := integrable.convolution_integrand
    (ContinuousLinearMap.lsmul ℝ ℝ) truncatedIntegrable
  have originalMeasurable : AEStronglyMeasurable
      (fun point : Plane × Plane => vorticity point.2 • biotSavartKernel (point.1 - point.2))
      (volume.prod volume) := integrable.aestronglyMeasurable.convolution_integrand
    (ContinuousLinearMap.lsmul ℝ ℝ) measurable_biotSavartKernel.aestronglyMeasurable
  apply (convolutionIntegrable.norm.const_mul bound).mono'
  · exact (continuousDerivative.comp continuous_fst).aestronglyMeasurable.norm.mul
      originalMeasurable.norm
  · filter_upwards [] with point
    by_cases outside : fderiv ℝ test point.1 = 0
    · simp only [outside, norm_zero, zero_mul]
      positivity
    · have inSupport : point.1 ∈ tsupport (fderiv ℝ test) :=
        subset_tsupport _ (Function.mem_support.mpr outside)
      have equality := biotSavart_integrand_eq_truncated supportBound
        (show ‖point.1‖ + radius < observationRadius + radius + 1 by
          linarith [observationBound point.1 inSupport]) point.2
      have boundAt := derivativeBound _ ⟨point.1, inSupport, rfl⟩
      change ‖‖fderiv ℝ test point.1‖ *
        ‖vorticity point.2 • biotSavartKernel (point.1 - point.2)‖‖ ≤
          bound * ‖vorticity point.2 • truncated (point.1 - point.2)‖
      dsimp only [truncated]
      rw [equality, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right boundAt (norm_nonneg _)

theorem integrable_biotSavart_test_integrand {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {test : Plane → ℝ} (smooth : ContDiff ℝ 1 test) (compact : HasCompactSupport test) :
    Integrable (fun point : Plane × Plane =>
      fderiv ℝ test point.1 (vorticity point.2 • biotSavartKernel (point.1 - point.2)))
      (volume.prod volume) := by
  have originalMeasurable : AEStronglyMeasurable
      (fun point : Plane × Plane => vorticity point.2 • biotSavartKernel (point.1 - point.2))
      (volume.prod volume) := integrable.aestronglyMeasurable.convolution_integrand
    (ContinuousLinearMap.lsmul ℝ ℝ) measurable_biotSavartKernel.aestronglyMeasurable
  apply (integrable_biotSavart_test_integrand_norm integrable supportBound smooth compact).mono'
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((smooth.continuous_fderiv (by simp)).comp continuous_fst).aestronglyMeasurable.prodMk
        originalMeasurable)
  · exact Filter.Eventually.of_forall fun point => (fderiv ℝ test point.1).le_opNorm _

theorem divergenceFree_biotSavart_of_integrable_support {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {test : Plane → ℝ} (smooth : ContDiff ℝ 1 test) (compact : HasCompactSupport test) :
    Integrable (fun position => fderiv ℝ test position (biotSavart vorticity position)) ∧
      (∫ position, fderiv ℝ test position (biotSavart vorticity position)) = 0 := by
  refine ⟨integrable_fderiv_apply_of_locallyIntegrable
    (locallyIntegrable_biotSavart_of_integrable_support integrable supportBound) smooth compact, ?_⟩
  have equality : ∀ᵐ position ∂(volume : Measure Plane),
      fderiv ℝ test position (biotSavart vorticity position) =
        ∫ source, fderiv ℝ test position
          (vorticity source • biotSavartKernel (position - source)) := by
    filter_upwards [biotSavartIntegrable_of_integrable_support integrable supportBound]
      with position convolutionIntegrable
    exact ((fderiv ℝ test position).integral_comp_comm convolutionIntegrable).symm
  rw [integral_congr_ae equality]
  rw [integral_integral_swap (integrable_biotSavart_test_integrand
    integrable supportBound smooth compact)]
  have innerZero : ∀ source : Plane,
      (∫ position, fderiv ℝ test position
        (vorticity source • biotSavartKernel (position - source))) = 0 := by
    intro source
    simp_rw [map_smul, smul_eq_mul]
    rw [integral_const_mul, integral_fderiv_shift_biotSavartKernel_eq_zero smooth compact, mul_zero]
  simp only [innerZero, integral_zero]

theorem divergenceFree_biotSavart_evolution {omega : Evolution}
    (integrable : ∀ time, 0 ≤ time → Integrable (omega time))
    (boundedSupport : ∀ time, 0 ≤ time → ∃ radius : ℝ,
      Function.support (omega time) ⊆ Metric.closedBall 0 radius) :
    DivergenceFree (fun time => biotSavart (omega time)) := by
  intro time nonnegative test smooth compact
  obtain ⟨radius, supportBound⟩ := boundedSupport time nonnegative
  exact divergenceFree_biotSavart_of_integrable_support
    (integrable time nonnegative) supportBound (smooth.of_le (by simp)) compact

theorem contDiff_biotSavart_of_contDiff_compactSupport {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity) :
    ContDiff ℝ ∞ (biotSavart vorticity) := by
  exact compact.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    smooth locallyIntegrable_biotSavartKernel

end EulerNonuniqueness
