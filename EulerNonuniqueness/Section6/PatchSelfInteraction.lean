import EulerNonuniqueness.Section8.BiotSavart
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem biotSavartKernel_neg (position : ℂ) :
    biotSavartKernel (-position) = -biotSavartKernel position := by
  simp [biotSavartKernel, mul_neg, neg_div]

theorem integrable_patch_pair_kernel {domain : Set ℂ} (measurable : MeasurableSet domain)
    {radius : ℝ} (bounded : domain ⊆ Metric.closedBall 0 radius) :
    Integrable (fun pair : ℂ × ℂ => biotSavartKernel (pair.1 - pair.2))
      ((volume.restrict domain).prod (volume.restrict domain)) := by
  have finite : volume domain < ⊤ := lt_of_le_of_lt (measure_mono bounded) measure_closedBall_lt_top
  have weight : Integrable (domain.indicator (fun _ : ℂ => (1 : ℝ))) :=
    (integrable_indicator_iff measurable).mpr (integrableOn_const.mpr (Or.inr finite))
  have truncated : Integrable ((Metric.ball 0 (2 * radius + 1)).indicator biotSavartKernel) :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_biotSavartKernel_ball _)
  have joint := weight.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) truncated
  have restricted := joint.integrableOn (s := domain ×ˢ domain)
  have actual : IntegrableOn (fun pair : ℂ × ℂ => biotSavartKernel (pair.1 - pair.2))
      (domain ×ˢ domain) (volume.prod volume) := by
    apply restricted.congr_fun _ (measurable.prod measurable)
    intro pair member
    have firstBound : ‖pair.1‖ ≤ radius := by simpa using bounded member.1
    have secondBound : ‖pair.2‖ ≤ radius := by simpa using bounded member.2
    have differenceBound : ‖pair.1 - pair.2‖ < 2 * radius + 1 :=
      lt_of_le_of_lt (norm_sub_le _ _) (by linarith)
    simp [Set.indicator_of_mem member.2, Set.indicator_of_mem
      (show pair.1 - pair.2 ∈ Metric.ball 0 (2 * radius + 1) by simpa using differenceBound)]
  simpa only [IntegrableOn, Measure.prod_restrict] using actual

theorem integral_patch_self_interaction {domain : Set ℂ} (measurable : MeasurableSet domain)
    {radius : ℝ} (bounded : domain ⊆ Metric.closedBall 0 radius) :
    (∫ position in domain, biotSavart (domain.indicator (fun _ => (1 : ℝ))) position) = 0 := by
  have joint := integrable_patch_pair_kernel measurable bounded
  have swapped := integral_integral_swap (μ := volume.restrict domain)
    (ν := volume.restrict domain) (f := fun position source : ℂ =>
      biotSavartKernel (position - source)) joint
  have antisymmetric : (∫ position in domain, ∫ source in domain,
      biotSavartKernel (source - position)) =
      -(∫ position in domain, ∫ source in domain, biotSavartKernel (position - source)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with position
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with source
    rw [← biotSavartKernel_neg]
    congr 1
    abel
  have zero : (∫ position in domain, ∫ source in domain, biotSavartKernel (position - source)) = 0 := by
    rw [antisymmetric] at swapped
    linear_combination (1 / 2 : ℂ) * swapped
  convert zero using 1
  apply integral_congr_ae
  filter_upwards [] with position
  simp only [biotSavart, ← integral_indicator measurable]
  apply integral_congr_ae
  filter_upwards [] with source
  by_cases member : source ∈ domain <;> simp [member]

theorem integral_patch_self_interaction_density {domain : Set ℂ}
    (measurable : MeasurableSet domain) {radius : ℝ}
    (bounded : domain ⊆ Metric.closedBall 0 radius) (density : ℝ) :
    (∫ position in domain, biotSavart (domain.indicator (fun _ => density)) position) = 0 := by
  have velocity (position : ℂ) :
      biotSavart (domain.indicator (fun _ => density)) position =
      density • biotSavart (domain.indicator (fun _ => (1 : ℝ))) position := by
    unfold biotSavart
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with source
    by_cases member : source ∈ domain <;> simp [member]
  simp_rw [velocity]
  rw [integral_smul, integral_patch_self_interaction measurable bounded, smul_zero]

end EulerNonuniqueness.Section6
