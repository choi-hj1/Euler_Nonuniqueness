import EulerNonuniqueness.Section8.TransportAnalyticCommutatorLimit
import EulerNonuniqueness.Section8.TransportAnalyticInitialTrace
import EulerNonuniqueness.Section8.SpacetimeMeasurability

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.measurable_mollification
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (index : ℕ) :
    Measurable (fun point : Icc (0 : ℝ) horizon × Plane => mollification (omega point.1) index point.2) :=
  (measurable_uncurry_of_continuous_of_measurable
    (fun time : Icc (0 : ℝ) horizon => (contDiff_mollification (hypotheses.integrable time.property) index).continuous)
    (fun position => (hypotheses.continuous_mollification_time index position).measurable)).comp measurable_swap

theorem TransportAnalyticHypotheses.measurable_biotSavart
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) :
    Measurable (fun point : Icc (0 : ℝ) horizon × Plane => biotSavart (omega point.1) point.2) :=
  (measurable_uncurry_of_continuous_of_measurable
    (fun time : Icc (0 : ℝ) horizon => hypotheses.continuous_biotSavart time.property)
    (fun position => (hypotheses.continuous_biotSavart_time position).measurable)).comp measurable_swap

theorem TransportAnalyticHypotheses.measurable_mollification_derivative
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (index : ℕ) (direction : Plane) :
    Measurable (fun point : Icc (0 : ℝ) horizon × Plane =>
      fderiv ℝ (mollification (omega point.1) index) point.2 direction) := by
  apply (measurable_uncurry_of_continuous_of_measurable
    (fun time : Icc (0 : ℝ) horizon =>
      ((contDiff_mollification (hypotheses.integrable time.property) index).continuous_fderiv (by simp)).clm_apply continuous_const)
    (fun position => (hypotheses.continuous_mollifiedDerivative_time
      (mollifierBump index).contDiff_normed (mollifierBump index).hasCompactSupport_normed position direction).measurable)).comp measurable_swap

theorem TransportAnalyticHypotheses.measurable_mollification_advectiveDerivative
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (index : ℕ) :
    Measurable (fun point : Icc (0 : ℝ) horizon × Plane =>
      fderiv ℝ (mollification (omega point.1) index) point.2 (biotSavart (omega point.1) point.2)) := by
  have result := ((Complex.continuous_re.measurable.comp hypotheses.measurable_biotSavart).mul
    (hypotheses.measurable_mollification_derivative index 1)).add
      ((Complex.continuous_im.measurable.comp hypotheses.measurable_biotSavart).mul
        (hypotheses.measurable_mollification_derivative index Complex.I))
  convert result using 1
  funext point
  rw [realLinearMap_apply_complex]
  rfl

theorem TransportAnalyticHypotheses.aestronglyMeasurable_transportCommutator
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon)
    (index : ℕ) :
    AEStronglyMeasurable (fun point : ℝ × Plane => transportCommutator ((mollifierBump index).normed volume)
      (biotSavart (omega point.1)) (omega point.1) point.2) (spacetimeMeasure horizon) :=
  aestronglyMeasurable_spacetime_of_measurable_Icc nonnegative
    (hypotheses.measurable_transportCommutator
      (mollifierBump index).contDiff_normed (mollifierBump index).hasCompactSupport_normed)

theorem TransportAnalyticHypotheses.integrable_transportCommutator_spacetime
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon)
    (index : ℕ) :
    Integrable (fun point : ℝ × Plane => transportCommutator ((mollifierBump index).normed volume)
      (biotSavart (omega point.1)) (omega point.1) point.2) (spacetimeMeasure horizon) := by
  have measurable := hypotheses.aestronglyMeasurable_transportCommutator nonnegative index
  obtain ⟨bound, boundNonnegative, bounded⟩ := hypotheses.uniform_integral_transportCommutator_mollifier_norm
  apply (integrable_prod_iff measurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
    exact (bounded index ⟨time, inside.1.le, inside.2.le⟩).1
  · apply (integrable_const bound).mono' measurable.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact (bounded index ⟨time, inside.1.le, inside.2.le⟩).2

end EulerNonuniqueness
