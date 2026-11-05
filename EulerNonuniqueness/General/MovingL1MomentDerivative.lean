import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace EulerNonuniqueness.General

theorem hasDerivAt_moving_L1_cross_zero
    {Domain : Type*} [MeasurableSpace Domain] {measure : Measure Domain}
    {density : ℝ → Domain → ℝ} {kernel : ℝ → Domain → ℂ} {time constant : ℝ}
    (densityIntegrable : ∀ᶠ current in 𝓝 time, Integrable (density current) measure)
    (densityLimit : Tendsto (fun current => eLpNorm (density current - density time) 1 measure)
      (𝓝 time) (𝓝 0))
    (kernelDifferenceMeasurable : ∀ᶠ current in 𝓝 time,
      AEStronglyMeasurable (fun position => kernel current position - kernel time position) measure)
    (kernelDifferenceBound : ∀ᶠ current in 𝓝 time, ∀ᵐ position ∂measure,
      density current position ≠ density time position →
      ‖kernel current position - kernel time position‖ ≤ constant * |current - time|) :
    HasDerivAt (fun current => ∫ position,
      (density current position - density time position) •
        (kernel current position - kernel time position) ∂measure) 0 time := by
  let error := fun current => ∫ position,
    (density current position - density time position) •
      (kernel current position - kernel time position) ∂measure
  have atTime : error time = 0 := by simp [error]
  have realLimit : Tendsto
      (fun current => (eLpNorm (density current - density time) 1 measure).toReal * constant)
      (𝓝[≠] time) (𝓝 0) := by
    have converted := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp densityLimit
    simpa only [ENNReal.toReal_zero, zero_mul] using
      (converted.mul_const constant).mono_left nhdsWithin_le_nhds
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply squeeze_zero_norm' _ realLimit
  filter_upwards [densityIntegrable.filter_mono nhdsWithin_le_nhds,
    kernelDifferenceMeasurable.filter_mono nhdsWithin_le_nhds,
    kernelDifferenceBound.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with current currentIntegrable measurable bounded different
  have sourceIntegrable := currentIntegrable.sub densityIntegrable.self_of_nhds
  have rawBound : ‖error current‖ ≤
      (eLpNorm (density current - density time) 1 measure).toReal * (constant * |current - time|) := by
    calc
      _ ≤ ∫ position, ‖density current position - density time position‖ *
          (constant * |current - time|) ∂measure := by
        apply norm_integral_le_of_norm_le (sourceIntegrable.norm.mul_const _)
        filter_upwards [bounded] with position bound
        by_cases equal : density current position = density time position
        · simp only [Pi.sub_apply, equal, sub_self, zero_smul, norm_zero, zero_mul, le_refl]
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (bound equal) (abs_nonneg _)
      _ = _ := by
        rw [integral_mul_const, eLpNorm_one_eq_lintegral_enorm]
        change (∫ position, ‖(density current - density time) position‖ ∂measure) * _ = _
        rw [integral_norm_eq_lintegral_enorm sourceIntegrable.aestronglyMeasurable]
  have nonzero : current - time ≠ 0 := sub_ne_zero.mpr different
  change ‖slope error time current‖ ≤ _
  rw [slope_def_module, atTime, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    |current - time|⁻¹ * ‖error current‖ ≤
        |current - time|⁻¹ * ((eLpNorm (density current - density time) 1 measure).toReal *
          (constant * |current - time|)) :=
      mul_le_mul_of_nonneg_left rawBound (inv_nonneg.mpr (abs_nonneg _))
    _ = _ := by field_simp; ring

theorem hasDerivAt_moving_L1_moment
    {Domain : Type*} [MeasurableSpace Domain] {measure : Measure Domain}
    {density : ℝ → Domain → ℝ} {kernel : ℝ → Domain → ℂ}
    {time constant : ℝ} {fixedRate movingRate : ℂ}
    (densityIntegrable : ∀ᶠ current in 𝓝 time, Integrable (density current) measure)
    (densityLimit : Tendsto (fun current => eLpNorm (density current - density time) 1 measure)
      (𝓝 time) (𝓝 0))
    (kernelDifferenceMeasurable : ∀ᶠ current in 𝓝 time,
      AEStronglyMeasurable (fun position => kernel current position - kernel time position) measure)
    (kernelDifferenceBound : ∀ᶠ current in 𝓝 time, ∀ᵐ position ∂measure,
      density current position ≠ density time position →
      ‖kernel current position - kernel time position‖ ≤ constant * |current - time|)
    (mixedIntegrable : ∀ᶠ current in 𝓝 time,
      Integrable (fun position => density current position • kernel current position) measure ∧
      Integrable (fun position => density current position • kernel time position) measure ∧
      Integrable (fun position => density time position • kernel current position) measure ∧
      Integrable (fun position => density time position • kernel time position) measure)
    (fixedDerivative : HasDerivAt (fun current => ∫ position,
      density current position • kernel time position ∂measure) fixedRate time)
    (movingDerivative : HasDerivAt (fun current => ∫ position,
      density time position • kernel current position ∂measure) movingRate time) :
    HasDerivAt (fun current => ∫ position, density current position • kernel current position ∂measure)
      (fixedRate + movingRate) time := by
  have cross := hasDerivAt_moving_L1_cross_zero densityIntegrable densityLimit
    kernelDifferenceMeasurable kernelDifferenceBound
  have combined := ((cross.add fixedDerivative).add movingDerivative).sub
    (hasDerivAt_const time (∫ position, density time position • kernel time position ∂measure))
  simp only [zero_add, sub_zero] at combined
  apply combined.congr_of_eventuallyEq
  filter_upwards [mixedIntegrable] with current integrable
  have crossIntegrable : Integrable (fun position =>
      (density current position - density time position) •
        (kernel current position - kernel time position)) measure := by
    convert ((integrable.1.sub integrable.2.1).sub integrable.2.2.1).add integrable.2.2.2 using 1
    funext position
    simp only [Pi.add_apply, Pi.sub_apply, sub_smul, smul_sub]
    abel
  have integrand : (fun position => density current position • kernel current position) =
      (((fun position => (density current position - density time position) •
          (kernel current position - kernel time position)) +
        (fun position => density current position • kernel time position)) +
        (fun position => density time position • kernel current position)) -
        (fun position => density time position • kernel time position) := by
    funext position
    simp only [Pi.add_apply, Pi.sub_apply, sub_smul, smul_sub]
    abel
  have first := integral_add crossIntegrable integrable.2.1
  have second := integral_add (crossIntegrable.add integrable.2.1) integrable.2.2.1
  have third := integral_sub ((crossIntegrable.add integrable.2.1).add integrable.2.2.1) integrable.2.2.2
  have result := third.trans (congrArg (fun value => value -
    ∫ position, density time position • kernel time position ∂measure) second)
  have result := result.trans (congrArg (fun value => value +
    (∫ position, density time position • kernel current position ∂measure) -
    ∫ position, density time position • kernel time position ∂measure) first)
  rw [integrand]
  exact result

end EulerNonuniqueness.General
