import EulerNonuniqueness.Section6.DiskExteriorStrain
import EulerNonuniqueness.Section6.KernelStrainSourceTaylor
import EulerNonuniqueness.Section6.PatchDeformationError

noncomputable section

open Set MeasureTheory
open scoped symmDiff

namespace EulerNonuniqueness.Section6

theorem kernelStrainSourceTaylorRemainder_integrableOn {domain : Set ℂ}
    (measurable : MeasurableSet domain) {center position : ℂ} {radius : ℝ}
    (bounded : domain ⊆ Metric.closedBall center radius) (positive : 0 < ‖position - center‖)
    (separated : 2 * radius ≤ ‖position - center‖) :
    IntegrableOn (kernelStrainSourceTaylorRemainder position center) domain := by
  have finite : volume domain < ⊤ := lt_of_le_of_lt (measure_mono bounded) measure_closedBall_lt_top
  have kernelIntegrable : IntegrableOn (biotSavartKernelStrain position) domain :=
    integrableOn_biotSavartKernelStrain_of_separation measurable finite (by positivity : 0 < ‖position - center‖ / 2) (by
      intro source member
      have sourceBound : ‖source - center‖ ≤ radius := by simpa [Metric.mem_closedBall, dist_eq_norm] using bounded member
      have triangle := norm_add_le (position - source) (source - center)
      rw [sub_add_sub_cancel] at triangle
      linarith)
  have constantIntegrable : IntegrableOn (fun _ : ℂ => biotSavartKernelStrain position center) domain :=
    integrableOn_const.mpr (Or.inr finite)
  have linearContinuous : Continuous (fun source : ℂ =>
      2 * (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star ((source - center) / (position - center) ^ 3)) := by fun_prop
  have linearIntegrable : IntegrableOn (fun source : ℂ =>
      2 * (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star ((source - center) / (position - center) ^ 3)) domain :=
    (linearContinuous.continuousOn.integrableOn_compact (isCompact_closedBall center radius)).mono_set bounded
  exact (kernelIntegrable.sub constantIntegrable).add linearIntegrable

theorem kernelStrainSourceTaylorRemainder_integral {domain : Set ℂ}
    (measurable : MeasurableSet domain) {center position : ℂ} {radius : ℝ}
    (bounded : domain ⊆ Metric.closedBall center radius)
    (centroid : (∫ source in domain, source - center) = 0)
    (positive : 0 < ‖position - center‖) (separated : 2 * radius ≤ ‖position - center‖) :
    (∫ source in domain, kernelStrainSourceTaylorRemainder position center source) =
      (∫ source in domain, biotSavartKernelStrain position source) -
        volume.real domain • biotSavartKernelStrain position center := by
  have finite : volume domain < ⊤ := lt_of_le_of_lt (measure_mono bounded) measure_closedBall_lt_top
  have kernelIntegrable : IntegrableOn (biotSavartKernelStrain position) domain :=
    integrableOn_biotSavartKernelStrain_of_separation measurable finite (by positivity : 0 < ‖position - center‖ / 2) (by
      intro source member
      have sourceBound : ‖source - center‖ ≤ radius := by simpa [Metric.mem_closedBall, dist_eq_norm] using bounded member
      have triangle := norm_add_le (position - source) (source - center)
      rw [sub_add_sub_cancel] at triangle
      linarith)
  have constantIntegrable : IntegrableOn (fun _ : ℂ => biotSavartKernelStrain position center) domain :=
    integrableOn_const.mpr (Or.inr finite)
  let linear := fun source : ℂ =>
    2 * (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star ((source - center) / (position - center) ^ 3)
  have linearContinuous : Continuous linear := by dsimp only [linear]; fun_prop
  have linearIntegrable : IntegrableOn linear domain :=
    (linearContinuous.continuousOn.integrableOn_compact (isCompact_closedBall center radius)).mono_set bounded
  have linearZero : (∫ source in domain, linear source) = 0 := by
    dsimp only [linear]
    simp only [Complex.star_def]
    rw [integral_const_mul, integral_conj, integral_div, centroid]
    simp
  change (∫ source in domain, biotSavartKernelStrain position source - biotSavartKernelStrain position center + linear source) = _
  rw [integral_add (f := fun source => biotSavartKernelStrain position source - biotSavartKernelStrain position center)
    (g := linear) (kernelIntegrable.sub constantIntegrable) linearIntegrable,
    integral_sub (f := biotSavartKernelStrain position) (g := fun _ => biotSavartKernelStrain position center)
      kernelIntegrable constantIntegrable, linearZero, add_zero, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ]

theorem integral_kernelStrain_patch_variation_bound {first second : Set ℂ}
    (firstMeasurable : MeasurableSet first) (secondMeasurable : MeasurableSet second)
    {center position : ℂ} {radius : ℝ}
    (firstBounded : first ⊆ Metric.closedBall center radius) (secondBounded : second ⊆ Metric.closedBall center radius)
    (sameArea : volume.real first = volume.real second)
    (firstCentroid : (∫ source in first, source - center) = 0)
    (secondCentroid : (∫ source in second, source - center) = 0)
    (positive : 0 < ‖position - center‖) (separated : 2 * radius ≤ ‖position - center‖) :
    ‖(∫ source in first, biotSavartKernelStrain position source) -
        (∫ source in second, biotSavartKernelStrain position source)‖ ≤
      volume.real (first ∆ second) * (8 * radius ^ 2 / (Real.pi * ‖position - center‖ ^ 4)) := by
  have differenceBounded : first ∆ second ⊆ Metric.closedBall center radius :=
    symmDiff_subset_union.trans (union_subset firstBounded secondBounded)
  have finite : volume (first ∆ second) < ⊤ :=
    lt_of_le_of_lt (measure_mono differenceBounded) measure_closedBall_lt_top
  have identity :
      (∫ source in first, biotSavartKernelStrain position source) -
        (∫ source in second, biotSavartKernelStrain position source) =
      (∫ source in first, kernelStrainSourceTaylorRemainder position center source) -
        (∫ source in second, kernelStrainSourceTaylorRemainder position center source) := by
    rw [kernelStrainSourceTaylorRemainder_integral firstMeasurable firstBounded firstCentroid positive separated,
      kernelStrainSourceTaylorRemainder_integral secondMeasurable secondBounded secondCentroid positive separated, sameArea]
    abel
  rw [identity]
  exact norm_patch_integral_difference_le firstMeasurable secondMeasurable finite
    (kernelStrainSourceTaylorRemainder_integrableOn firstMeasurable firstBounded positive separated)
    (kernelStrainSourceTaylorRemainder_integrableOn secondMeasurable secondBounded positive separated)
    (fun source member => kernelStrainSourceTaylorRemainder_bound positive
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using differenceBounded member) separated)

theorem vorticityComplexStrain_indicator {domain : Set ℂ} (measurable : MeasurableSet domain)
    (density : ℝ) (position : ℂ) :
    vorticityComplexStrain (domain.indicator (fun _ => density)) position =
      density • (∫ source in domain, biotSavartKernelStrain position source) := by
  have identity : (fun source => domain.indicator (fun _ => density) source • biotSavartKernelStrain position source) =
      fun source => density • domain.indicator (biotSavartKernelStrain position) source := by
    funext source
    by_cases member : source ∈ domain <;> simp [member]
  rw [vorticityComplexStrain, identity, integral_smul, integral_indicator measurable]

theorem vorticityComplexStrain_patch_relative_deformation_bound {domain : Set ℂ}
    (measurable : MeasurableSet domain) (center centroid position : ℂ) {radius deformation : ℝ}
    (radiusPositive : 0 < radius) (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (lower : Metric.ball center (radius * (1 - deformation)) ⊆ domain)
    (upper : domain ⊆ Metric.ball center (radius * (1 + deformation)))
    (area : volume.real domain = Real.pi * radius ^ 2)
    (centroidMoment : (∫ source in domain, source - centroid) = 0)
    (separated : 4 * radius ≤ ‖position - centroid‖) (density : ℝ) :
    ‖vorticityComplexStrain (domain.indicator (fun _ => density)) position -
        (density * (Real.pi * radius ^ 2)) • biotSavartKernelStrain position centroid‖ ≤
      1024 * |density * (Real.pi * radius ^ 2)| * radius ^ 2 * deformation /
        (Real.pi * ‖position - centroid‖ ^ 4) := by
  have geometry := patch_actual_centroid_geometry measurable center centroid radiusPositive nonnegative small lower upper area centroidMoment
  have positive : 0 < ‖position - centroid‖ := by linarith
  have diskBounded : Metric.ball centroid radius ⊆ Metric.closedBall centroid (2 * radius) := by
    intro source member
    have bound : ‖source - centroid‖ < radius := by simpa [Metric.mem_ball, dist_eq_norm] using member
    simpa [Metric.mem_closedBall, dist_eq_norm] using bound.le.trans (by linarith : radius ≤ 2 * radius)
  have diskArea : volume.real (Metric.ball centroid radius) = Real.pi * radius ^ 2 := by
    rw [Measure.real, Paper.volume_complex_ball_of_nonneg centroid radiusPositive.le, ENNReal.toReal_ofReal (by positivity)]
  have estimate := integral_kernelStrain_patch_variation_bound measurable measurableSet_ball geometry.2.1 diskBounded
    (area.trans diskArea.symm) centroidMoment (integral_ball_centered_identity centroid radius) positive (by linarith)
  rw [integral_ball_biotSavartKernelStrain_exterior centroid position radiusPositive (by linarith)] at estimate
  rw [vorticityComplexStrain_indicator measurable, mul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left estimate (abs_nonneg density)).trans
  have multiplied := mul_le_mul_of_nonneg_right geometry.2.2
    (show 0 ≤ |density| * (8 * (2 * radius) ^ 2 / (Real.pi * ‖position - centroid‖ ^ 4)) by positivity)
  calc
    _ = volume.real (domain ∆ Metric.ball centroid radius) *
        (|density| * (8 * (2 * radius) ^ 2 / (Real.pi * ‖position - centroid‖ ^ 4))) := by ring
    _ ≤ (32 * Real.pi * radius ^ 2 * deformation) *
        (|density| * (8 * (2 * radius) ^ 2 / (Real.pi * ‖position - centroid‖ ^ 4))) := multiplied
    _ = _ := by
      rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.pi * radius ^ 2 by positivity)]
      ring

end EulerNonuniqueness.Section6
