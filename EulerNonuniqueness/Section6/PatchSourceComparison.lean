import EulerNonuniqueness.Section6.PatchKernelTaylor

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem integrableOn_patch_source_kernel {domain : Set ℂ} {center position : ℂ} {radius : ℝ}
    (bounded : domain ⊆ Metric.closedBall center radius)
    (distancePositive : 0 < ‖position - center‖)
    (separated : 2 * radius ≤ ‖position - center‖) :
    IntegrableOn (fun source => biotSavartKernel (position - source)) domain := by
  have continuous : ContinuousOn (fun source => biotSavartKernel (position - source))
      (Metric.closedBall center radius) := by
    intro source member
    have sourceBound : ‖source - center‖ ≤ radius := by simpa [dist_eq_norm] using member
    have nonzero : position - source ≠ 0 := by
      intro equality
      have positionEquality : position = source := sub_eq_zero.mp equality
      rw [positionEquality] at distancePositive separated
      linarith
    exact ((continuousAt_biotSavartKernel nonzero).comp
      (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
  exact (continuous.integrableOn_compact (isCompact_closedBall center radius)).mono_set bounded

theorem patch_source_centroid_comparison {domain : Set ℂ}
    (measurable : MeasurableSet domain) {center position : ℂ} {radius : ℝ}
    (bounded : domain ⊆ Metric.closedBall center radius)
    (centroid : (∫ source in domain, source - center) = 0)
    (distancePositive : 0 < ‖position - center‖)
    (separated : 2 * radius ≤ ‖position - center‖) :
    ‖(∫ source in domain, biotSavartKernel (position - source)) -
        volume.real domain • biotSavartKernel (position - center)‖ ≤
      volume.real domain * radius ^ 2 / (Real.pi * ‖position - center‖ ^ 3) := by
  have finite : volume domain < ⊤ := lt_of_le_of_lt (measure_mono bounded) measure_closedBall_lt_top
  let linear := fun source : ℂ => (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
    starRingEnd ℂ ((source - center) / (position - center) ^ 2)
  have linearContinuous : Continuous linear := by
    dsimp [linear]
    change Continuous (fun source => (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
      Complex.conjCLE ((source - center) / (position - center) ^ 2))
    fun_prop
  have linearIntegrable : IntegrableOn linear domain :=
    (linearContinuous.continuousOn.integrableOn_compact (isCompact_closedBall center radius)).mono_set bounded
  have kernelIntegrable := integrableOn_patch_source_kernel bounded distancePositive separated
  have constantIntegrable : IntegrableOn (fun _ : ℂ => biotSavartKernel (position - center)) domain :=
    integrableOn_const.mpr (Or.inr finite)
  have linearZero : (∫ source in domain, linear source) = 0 := by
    dsimp only [linear]
    rw [integral_const_mul, integral_conj, integral_div, centroid]
    simp
  have integralIdentity :
      (∫ source in domain, biotSavartKernel (position - source) -
        biotSavartKernel (position - center) - linear source) =
      (∫ source in domain, biotSavartKernel (position - source)) -
        volume.real domain • biotSavartKernel (position - center) := by
    rw [integral_sub (f := fun source : ℂ => biotSavartKernel (position - source) -
      biotSavartKernel (position - center)) (g := linear)
      (kernelIntegrable.sub constantIntegrable) linearIntegrable,
      integral_sub (f := fun source : ℂ => biotSavartKernel (position - source))
        (g := fun _ : ℂ => biotSavartKernel (position - center))
        kernelIntegrable constantIntegrable, linearZero, sub_zero, integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ]
  rw [← integralIdentity]
  have estimate := norm_integral_le_of_norm_le
    (μ := volume.restrict domain)
    (f := fun source => biotSavartKernel (position - source) -
      biotSavartKernel (position - center) - linear source)
    (g := fun _ => radius ^ 2 / (Real.pi * ‖position - center‖ ^ 3))
    (integrableOn_const.mpr (Or.inr finite))
    (by
      filter_upwards [ae_restrict_mem measurable] with source member
      exact biotSavart_source_taylor_bound distancePositive
        (by simpa [dist_eq_norm] using bounded member) separated)
  simpa only [integral_const, smul_eq_mul, Measure.restrict_apply_univ,
    Measure.real, mul_div_assoc] using estimate

theorem biotSavart_patch_centroid_comparison {domain : Set ℂ}
    (measurable : MeasurableSet domain) {center position : ℂ} {radius : ℝ}
    (bounded : domain ⊆ Metric.closedBall center radius)
    (centroid : (∫ source in domain, source - center) = 0)
    (distancePositive : 0 < ‖position - center‖)
    (separated : 2 * radius ≤ ‖position - center‖) (density : ℝ) :
    ‖biotSavart (domain.indicator (fun _ => density)) position -
        (density * volume.real domain) • biotSavartKernel (position - center)‖ ≤
      |density| * volume.real domain * radius ^ 2 / (Real.pi * ‖position - center‖ ^ 3) := by
  have velocity : biotSavart (domain.indicator (fun _ => density)) position =
      density • (∫ source in domain, biotSavartKernel (position - source)) := by
    rw [← integral_smul, ← integral_indicator measurable]
    unfold biotSavart
    apply integral_congr_ae
    filter_upwards [] with source
    by_cases member : source ∈ domain <;> simp [member]
  rw [velocity, mul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]
  have bound := mul_le_mul_of_nonneg_left
    (patch_source_centroid_comparison measurable bounded centroid distancePositive separated)
    (abs_nonneg density)
  simpa only [mul_div_assoc, mul_assoc] using bound

end EulerNonuniqueness.Section6
