import EulerNonuniqueness.Section6.PatchSelfInteraction

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem integrable_patch_cross_kernel {first second : Set ℂ}
    (firstMeasurable : MeasurableSet first) (secondMeasurable : MeasurableSet second)
    {radius : ℝ} (firstBounded : first ⊆ Metric.closedBall 0 radius)
    (secondBounded : second ⊆ Metric.closedBall 0 radius) :
    Integrable (fun pair : ℂ × ℂ => biotSavartKernel (pair.1 - pair.2))
      ((volume.restrict first).prod (volume.restrict second)) := by
  have joint := integrable_patch_pair_kernel (firstMeasurable.union secondMeasurable)
    (union_subset firstBounded secondBounded)
  have unionIntegrable : IntegrableOn
      (fun pair : ℂ × ℂ => biotSavartKernel (pair.1 - pair.2))
      ((first ∪ second) ×ˢ (first ∪ second)) (volume.prod volume) := by
    simpa only [IntegrableOn, Measure.prod_restrict] using joint
  have restricted := unionIntegrable.mono_set
    (Set.prod_mono (subset_union_left : first ⊆ first ∪ second)
      (subset_union_right : second ⊆ first ∪ second))
  simpa only [IntegrableOn, Measure.prod_restrict] using restricted

theorem integral_patch_cross_interaction {first second : Set ℂ}
    (firstMeasurable : MeasurableSet first) (secondMeasurable : MeasurableSet second)
    {radius : ℝ} (firstBounded : first ⊆ Metric.closedBall 0 radius)
    (secondBounded : second ⊆ Metric.closedBall 0 radius) :
    (∫ position in first, ∫ source in second, biotSavartKernel (position - source)) +
      (∫ position in second, ∫ source in first, biotSavartKernel (position - source)) = 0 := by
  have joint := integrable_patch_cross_kernel firstMeasurable secondMeasurable firstBounded secondBounded
  have swapped := integral_integral_swap (μ := volume.restrict first)
    (ν := volume.restrict second) (f := fun position source : ℂ =>
      biotSavartKernel (position - source)) joint
  rw [swapped]
  have opposite : (∫ source in second, ∫ position in first, biotSavartKernel (position - source)) =
      -(∫ source in second, ∫ position in first, biotSavartKernel (source - position)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with source
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with position
    rw [← biotSavartKernel_neg]
    congr 1
    abel
  rw [opposite, neg_add_cancel]

theorem biotSavart_indicator_density_integral {domain : Set ℂ}
    (measurable : MeasurableSet domain) (density : ℝ) (position : ℂ) :
    biotSavart (domain.indicator (fun _ => density)) position =
      density • (∫ source in domain, biotSavartKernel (position - source)) := by
  unfold biotSavart
  rw [← integral_smul, ← integral_indicator measurable]
  apply integral_congr_ae
  filter_upwards [] with source
  by_cases member : source ∈ domain <;> simp [member]

theorem integral_patch_cross_interaction_density {first second : Set ℂ}
    (firstMeasurable : MeasurableSet first) (secondMeasurable : MeasurableSet second)
    {radius : ℝ} (firstBounded : first ⊆ Metric.closedBall 0 radius)
    (secondBounded : second ⊆ Metric.closedBall 0 radius) (firstDensity secondDensity : ℝ) :
    firstDensity • (∫ position in first,
        biotSavart (second.indicator (fun _ => secondDensity)) position) +
      secondDensity • (∫ position in second,
        biotSavart (first.indicator (fun _ => firstDensity)) position) = 0 := by
  simp_rw [biotSavart_indicator_density_integral secondMeasurable,
    biotSavart_indicator_density_integral firstMeasurable]
  rw [integral_smul, integral_smul, smul_smul, smul_smul,
    mul_comm secondDensity firstDensity, ← smul_add,
    integral_patch_cross_interaction firstMeasurable secondMeasurable firstBounded secondBounded,
    smul_zero]

end EulerNonuniqueness.Section6
