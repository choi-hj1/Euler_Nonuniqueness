import EulerNonuniqueness.Section6.PatchSourceComparison
import EulerNonuniqueness.Section6.DiskExteriorBiotSavart
import EulerNonuniqueness.Section3.DiskLp

noncomputable section

open Set MeasureTheory
open scoped symmDiff

namespace EulerNonuniqueness.Section6

theorem norm_patch_integral_difference_le {first second : Set ℂ}
    (firstMeasurable : MeasurableSet first) (secondMeasurable : MeasurableSet second)
    (finite : volume (first ∆ second) < ⊤) {function : ℂ → ℂ}
    (firstIntegrable : IntegrableOn function first) (secondIntegrable : IntegrableOn function second)
    {bound : ℝ} (bounded : ∀ position ∈ first ∆ second, ‖function position‖ ≤ bound) :
    ‖(∫ position in first, function position) - (∫ position in second, function position)‖ ≤
      volume.real (first ∆ second) * bound := by
  have firstIndicator := (integrable_indicator_iff firstMeasurable).mpr firstIntegrable
  have secondIndicator := (integrable_indicator_iff secondMeasurable).mpr secondIntegrable
  have majorant : Integrable ((first ∆ second).indicator (fun _ : ℂ => bound)) :=
    (integrable_indicator_iff (firstMeasurable.symmDiff secondMeasurable)).mpr
      (integrableOn_const.mpr (Or.inr finite))
  have estimate := norm_integral_le_of_norm_le
    (f := fun position => first.indicator function position - second.indicator function position)
    majorant (by
      filter_upwards [] with position
      by_cases inFirst : position ∈ first <;> by_cases inSecond : position ∈ second
      · simp [inFirst, inSecond, Set.mem_symmDiff]
      · have bound := bounded position (Set.mem_symmDiff.mpr (Or.inl ⟨inFirst, inSecond⟩))
        simpa [inFirst, inSecond, Set.mem_symmDiff] using bound
      · have bound := bounded position (Set.mem_symmDiff.mpr (Or.inr ⟨inSecond, inFirst⟩))
        simpa [inFirst, inSecond, Set.mem_symmDiff] using bound
      · simp [inFirst, inSecond, Set.mem_symmDiff])
  rw [integral_sub (f := first.indicator function) (g := second.indicator function)
    firstIndicator secondIndicator, integral_indicator firstMeasurable, integral_indicator secondMeasurable,
    integral_indicator (firstMeasurable.symmDiff secondMeasurable), integral_const] at estimate
  simpa only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul] using estimate

def sourceTaylorRemainder (position center source : ℂ) : ℂ :=
  biotSavartKernel (position - source) - biotSavartKernel (position - center) -
    (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * starRingEnd ℂ ((source - center) / (position - center) ^ 2)

theorem sourceTaylorRemainder_integrableOn {domain : Set ℂ} {position center : ℂ} {radius : ℝ}
    (bounded : domain ⊆ Metric.closedBall center radius)
    (distancePositive : 0 < ‖position - center‖) (separated : 2 * radius ≤ ‖position - center‖) :
    IntegrableOn (sourceTaylorRemainder position center) domain := by
  have finite : volume domain < ⊤ := lt_of_le_of_lt (measure_mono bounded) measure_closedBall_lt_top
  have linearContinuous : Continuous (fun source : ℂ =>
      (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * starRingEnd ℂ ((source - center) / (position - center) ^ 2)) := by
    change Continuous (fun source : ℂ =>
      (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * Complex.conjCLE ((source - center) / (position - center) ^ 2))
    fun_prop
  have linearIntegrable : IntegrableOn (fun source : ℂ =>
      (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * starRingEnd ℂ ((source - center) / (position - center) ^ 2)) domain :=
    (linearContinuous.continuousOn.integrableOn_compact
    (isCompact_closedBall center radius)).mono_set bounded
  exact ((integrableOn_patch_source_kernel bounded distancePositive separated).sub
    (integrableOn_const.mpr (Or.inr finite))).sub linearIntegrable

theorem sourceTaylorRemainder_integral {domain : Set ℂ} {position center : ℂ} {radius : ℝ}
    (bounded : domain ⊆ Metric.closedBall center radius)
    (centroid : (∫ source in domain, source - center) = 0)
    (distancePositive : 0 < ‖position - center‖) (separated : 2 * radius ≤ ‖position - center‖) :
    (∫ source in domain, sourceTaylorRemainder position center source) =
      (∫ source in domain, biotSavartKernel (position - source)) -
        volume.real domain • biotSavartKernel (position - center) := by
  have finite : volume domain < ⊤ := lt_of_le_of_lt (measure_mono bounded) measure_closedBall_lt_top
  have kernelIntegrable := integrableOn_patch_source_kernel bounded distancePositive separated
  have constantIntegrable : IntegrableOn (fun _ : ℂ => biotSavartKernel (position - center)) domain :=
    integrableOn_const.mpr (Or.inr finite)
  let linear := fun source : ℂ => (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
    starRingEnd ℂ ((source - center) / (position - center) ^ 2)
  have linearIntegrable : IntegrableOn linear domain := by
    apply ((kernelIntegrable.sub constantIntegrable).sub
      (sourceTaylorRemainder_integrableOn bounded distancePositive separated)).congr
    exact Filter.Eventually.of_forall fun source => by dsimp [sourceTaylorRemainder, linear]; abel
  have linearZero : (∫ source in domain, linear source) = 0 := by
    dsimp only [linear]
    rw [integral_const_mul, integral_conj, integral_div, centroid]
    simp
  change (∫ source in domain, biotSavartKernel (position - source) -
    biotSavartKernel (position - center) - linear source) = _
  rw [integral_sub (f := fun source : ℂ => biotSavartKernel (position - source) -
    biotSavartKernel (position - center)) (g := linear)
    (kernelIntegrable.sub constantIntegrable) linearIntegrable,
    integral_sub (f := fun source : ℂ => biotSavartKernel (position - source))
      (g := fun _ : ℂ => biotSavartKernel (position - center))
      kernelIntegrable constantIntegrable, linearZero, sub_zero, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ]

theorem biotSavart_indicator_eq_smul_setIntegral {domain : Set ℂ}
    (measurable : MeasurableSet domain) (density : ℝ) (position : ℂ) :
    biotSavart (domain.indicator (fun _ => density)) position =
      density • (∫ source in domain, biotSavartKernel (position - source)) := by
  rw [← integral_smul, ← integral_indicator measurable]
  unfold biotSavart
  apply integral_congr_ae
  filter_upwards [] with source
  by_cases member : source ∈ domain <;> simp [member]

theorem biotSavart_patch_variation_bound {first second : Set ℂ}
    (firstMeasurable : MeasurableSet first) (secondMeasurable : MeasurableSet second)
    {center position : ℂ} {radius : ℝ}
    (firstBounded : first ⊆ Metric.closedBall center radius)
    (secondBounded : second ⊆ Metric.closedBall center radius)
    (sameArea : volume.real first = volume.real second)
    (firstCentroid : (∫ source in first, source - center) = 0)
    (secondCentroid : (∫ source in second, source - center) = 0)
    (distancePositive : 0 < ‖position - center‖) (separated : 2 * radius ≤ ‖position - center‖)
    (density : ℝ) :
    ‖biotSavart (first.indicator (fun _ => density)) position -
        biotSavart (second.indicator (fun _ => density)) position‖ ≤
      |density| * volume.real (first ∆ second) * radius ^ 2 /
        (Real.pi * ‖position - center‖ ^ 3) := by
  have differenceBounded : first ∆ second ⊆ Metric.closedBall center radius := by
    intro source member
    rcases Set.mem_symmDiff.mp member with member | member
    · exact firstBounded member.1
    · exact secondBounded member.1
  have finite : volume (first ∆ second) < ⊤ :=
    lt_of_le_of_lt (measure_mono differenceBounded) measure_closedBall_lt_top
  have firstIdentity := sourceTaylorRemainder_integral firstBounded firstCentroid distancePositive separated
  have secondIdentity := sourceTaylorRemainder_integral secondBounded secondCentroid distancePositive separated
  have integralDifference :
      (∫ source in first, biotSavartKernel (position - source)) -
        (∫ source in second, biotSavartKernel (position - source)) =
      (∫ source in first, sourceTaylorRemainder position center source) -
        (∫ source in second, sourceTaylorRemainder position center source) := by
    rw [firstIdentity, secondIdentity, sameArea]
    abel
  rw [biotSavart_indicator_eq_smul_setIntegral firstMeasurable,
    biotSavart_indicator_eq_smul_setIntegral secondMeasurable, ← smul_sub,
    integralDifference, norm_smul, Real.norm_eq_abs]
  have estimate := norm_patch_integral_difference_le firstMeasurable secondMeasurable finite
    (sourceTaylorRemainder_integrableOn firstBounded distancePositive separated)
    (sourceTaylorRemainder_integrableOn secondBounded distancePositive separated)
    (fun source member => biotSavart_source_taylor_bound distancePositive
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using differenceBounded member) separated)
  simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left estimate (abs_nonneg density)

theorem integral_centeredBall_identity (radius : ℝ) :
    (∫ source in Metric.ball (0 : ℂ) radius, source) = 0 := by
  have substitution := (volume.measurePreserving_sub_left (0 : ℂ)).setIntegral_preimage_emb
    (Homeomorph.subLeft (0 : ℂ)).toMeasurableEquiv.measurableEmbedding
    (fun source : ℂ => source) (Metric.ball (0 : ℂ) radius)
  have preimage : (fun source : ℂ => 0 - source) ⁻¹' Metric.ball (0 : ℂ) radius =
      Metric.ball (0 : ℂ) radius := by
    ext source
    simp [Metric.mem_ball]
  rw [preimage] at substitution
  simp only [zero_sub] at substitution
  rw [integral_neg (fun source : ℂ => source)] at substitution
  linear_combination (-1 / 2 : ℂ) * substitution

theorem integral_ball_centered_identity (center : ℂ) (radius : ℝ) :
    (∫ source in Metric.ball center radius, source - center) = 0 := by
  have substitution := (measurePreserving_add_left (volume : Measure ℂ) center).setIntegral_preimage_emb
    (Homeomorph.addLeft center).toMeasurableEquiv.measurableEmbedding
    (fun source : ℂ => source - center) (Metric.ball center radius)
  have preimage : (fun source : ℂ => center + source) ⁻¹' Metric.ball center radius =
      Metric.ball (0 : ℂ) radius := by
    ext source
    simp [Metric.mem_ball, dist_eq_norm]
  rw [preimage] at substitution
  have normalize (source : ℂ) : center + source - center = source := by abel
  simp_rw [normalize] at substitution
  exact substitution.symm.trans (integral_centeredBall_identity radius)

theorem biotSavart_patch_disk_deformation_bound {domain : Set ℂ}
    (measurable : MeasurableSet domain) {center position : ℂ} {radius enclosingRadius : ℝ}
    (radiusPositive : 0 < radius) (radiusBound : radius ≤ enclosingRadius)
    (bounded : domain ⊆ Metric.closedBall center enclosingRadius)
    (area : volume.real domain = Real.pi * radius ^ 2)
    (centroid : (∫ source in domain, source - center) = 0)
    (distancePositive : 0 < ‖position - center‖)
    (separated : 2 * enclosingRadius ≤ ‖position - center‖) (density : ℝ) :
    ‖biotSavart (domain.indicator (fun _ => density)) position -
        (density * (Real.pi * radius ^ 2)) • biotSavartKernel (position - center)‖ ≤
      |density| * volume.real (domain ∆ Metric.ball center radius) * enclosingRadius ^ 2 /
        (Real.pi * ‖position - center‖ ^ 3) := by
  have diskArea : volume.real (Metric.ball center radius) = Real.pi * radius ^ 2 := by
    rw [Measure.real, Paper.volume_complex_ball_of_nonneg center radiusPositive.le,
      ENNReal.toReal_ofReal (by positivity)]
  have diskBounded : Metric.ball center radius ⊆ Metric.closedBall center enclosingRadius := by
    intro source member
    have sourceBound : ‖source - center‖ < radius := by simpa [Metric.mem_ball, dist_eq_norm] using member
    simpa [Metric.mem_closedBall, dist_eq_norm] using sourceBound.le.trans radiusBound
  have estimate := biotSavart_patch_variation_bound measurable measurableSet_ball bounded diskBounded
    (area.trans diskArea.symm) centroid (integral_ball_centered_identity center radius)
    distancePositive separated density
  rw [biotSavart_disk_exterior center position radiusPositive (by linarith)] at estimate
  exact estimate

end EulerNonuniqueness.Section6
