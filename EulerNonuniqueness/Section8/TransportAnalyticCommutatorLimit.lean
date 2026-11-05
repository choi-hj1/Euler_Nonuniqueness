import EulerNonuniqueness.Section8.TransportAnalyticCommutator

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

attribute [local instance] Measure.Subtype.measureSpace

theorem TransportAnalyticHypotheses.integrable_transportCommutator_mollifier_prod
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    (timeMeasure : Measure (Icc (0 : ℝ) horizon)) [IsFiniteMeasure timeMeasure]
    (mollifierIndex : ℕ) :
    Integrable (fun point : Icc (0 : ℝ) horizon × Plane =>
      transportCommutator ((mollifierBump mollifierIndex).normed volume)
        (biotSavart (omega point.1)) (omega point.1) point.2) (timeMeasure.prod volume) := by
  have measurable := (hypotheses.measurable_transportCommutator
    ((mollifierBump (Space := Plane) mollifierIndex).contDiff_normed (μ := volume))
    ((mollifierBump (Space := Plane) mollifierIndex).hasCompactSupport_normed (μ := volume))).stronglyMeasurable
  obtain ⟨bound, nonnegative, bounded⟩ := hypotheses.uniform_integral_transportCommutator_mollifier_norm
  apply (integrable_prod_iff measurable.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun time => (bounded mollifierIndex time).1
  · apply (integrable_const bound).mono' measurable.norm.integral_prod_right'.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun time => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (bounded mollifierIndex time).2

theorem TransportAnalyticHypotheses.tendsto_integral_transportCommutator_mollifier_norm
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    (timeMeasure : Measure (Icc (0 : ℝ) horizon)) [IsFiniteMeasure timeMeasure] :
    Tendsto (fun mollifierIndex => ∫ time : Icc (0 : ℝ) horizon, (∫ position : Plane,
      ‖transportCommutator ((mollifierBump mollifierIndex).normed volume)
        (biotSavart (omega time)) (omega time) position‖) ∂timeMeasure) atTop (𝓝 0) := by
  obtain ⟨radius, positive, supported⟩ := hypotheses.supported
  obtain ⟨bound, nonnegative, bounded⟩ := hypotheses.uniform_integral_transportCommutator_mollifier_norm
  have zeroIntegral : (∫ _ : Icc (0 : ℝ) horizon, (0 : ℝ) ∂timeMeasure) = 0 := by simp
  conv_rhs => rw [← zeroIntegral]
  apply tendsto_integral_of_dominated_convergence (fun _ => bound)
  · intro mollifierIndex
    exact (hypotheses.measurable_transportCommutator
      ((mollifierBump (Space := Plane) mollifierIndex).contDiff_normed (μ := volume))
      ((mollifierBump (Space := Plane) mollifierIndex).hasCompactSupport_normed (μ := volume))).norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  · exact integrable_const bound
  · intro mollifierIndex
    exact Filter.Eventually.of_forall fun time => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (bounded mollifierIndex time).2
  · filter_upwards [] with time
    exact EulerNonuniqueness.tendsto_integral_transportCommutator_mollifier_norm positive.le
      (fun exponent bound => hypotheses.membership exponent bound time time.property)
      (supported time time.property) (hypotheses.zeroMean time time.property)

theorem TransportAnalyticHypotheses.tendsto_setIntegral_transportCommutator_mollifier_norm
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) :
    Tendsto (fun mollifierIndex => ∫ time in Icc (0 : ℝ) horizon, (∫ position : Plane,
      ‖transportCommutator ((mollifierBump mollifierIndex).normed volume)
        (biotSavart (omega time)) (omega time) position‖)) atTop (𝓝 0) := by
  letI : IsFiniteMeasure (volume : Measure (Icc (0 : ℝ) horizon)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  have result := hypotheses.tendsto_integral_transportCommutator_mollifier_norm
    (volume : Measure (Icc (0 : ℝ) horizon))
  apply result.congr'
  filter_upwards [] with mollifierIndex
  exact integral_subtype (s := Icc (0 : ℝ) horizon) measurableSet_Icc
    (fun time => ∫ position : Plane, ‖transportCommutator ((mollifierBump mollifierIndex).normed volume)
      (biotSavart (omega time)) (omega time) position‖)

end EulerNonuniqueness
