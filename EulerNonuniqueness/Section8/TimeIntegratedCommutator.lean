import EulerNonuniqueness.Section8.TimeCommutator

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

attribute [local instance] Measure.Subtype.measureSpace

theorem LocalCompactnessHypotheses.uniform_integral_transportCommutator_mollifier_norm
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ index mollifierIndex (time : Icc (0 : ℝ) horizon),
      Integrable (transportCommutator ((mollifierBump mollifierIndex).normed volume)
        (biotSavart (sequence index time)) (sequence index time)) ∧
      (∫ position, ‖transportCommutator ((mollifierBump mollifierIndex).normed volume)
        (biotSavart (sequence index time)) (sequence index time) position‖) ≤ bound := by
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.2.1
  obtain ⟨normBound, normBoundFinite, normBounded⟩ :=
    hypotheses.uniform_eLpNorm_bound horizonNonnegative (by norm_num : (1 : ℝ) ≤ 2)
  let moment : ℝ := ∫ offset : Plane, ‖fderiv ℝ ((mollifierBump 0).normed volume) offset‖ * ‖offset‖
  have momentNonnegative : 0 ≤ moment := integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨moment * (2 * normBound.toReal ^ 2), by positivity, ?_⟩
  intro index mollifierIndex time
  have members := fun exponent bound => ((hypotheses.2.2 index).2.2.2 exponent bound time time.property).1
  have result := integral_transportCommutator_mollifier_norm_le radiusPositive.le members
    (supported index time time.property) ((hypotheses.2.2 index).2.2.1 time time.property).2 mollifierIndex
  refine ⟨result.1, result.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ momentNonnegative
  have sourceBound : (eLpNorm (sequence index time) 2 volume).toReal ≤ normBound.toReal :=
    ENNReal.toReal_mono normBoundFinite.ne (by simpa using normBounded index time time.property)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg sourceBound 2) (by norm_num)

theorem LocalCompactnessHypotheses.integrable_transportCommutator_mollifier_prod
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon)
    (timeMeasure : Measure (Icc (0 : ℝ) horizon)) [IsFiniteMeasure timeMeasure]
    (index mollifierIndex : ℕ) :
    Integrable (fun point : Icc (0 : ℝ) horizon × Plane =>
      transportCommutator ((mollifierBump mollifierIndex).normed volume)
        (biotSavart (sequence index point.1)) (sequence index point.1) point.2)
      (timeMeasure.prod volume) := by
  have measurable := (hypotheses.measurable_transportCommutator horizonNonnegative index
    ((mollifierBump (Space := Plane) mollifierIndex).contDiff_normed (μ := volume))
    ((mollifierBump (Space := Plane) mollifierIndex).hasCompactSupport_normed (μ := volume))).stronglyMeasurable
  obtain ⟨bound, boundNonnegative, bounded⟩ :=
    hypotheses.uniform_integral_transportCommutator_mollifier_norm horizonNonnegative
  apply (integrable_prod_iff measurable.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun time => (bounded index mollifierIndex time).1
  · apply (integrable_const bound).mono' measurable.norm.integral_prod_right'.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun time => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (bounded index mollifierIndex time).2

theorem LocalCompactnessHypotheses.tendsto_integral_transportCommutator_mollifier_norm
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon)
    (timeMeasure : Measure (Icc (0 : ℝ) horizon)) [IsFiniteMeasure timeMeasure] (index : ℕ) :
    Tendsto (fun mollifierIndex => ∫ time : Icc (0 : ℝ) horizon, (∫ position : Plane,
      ‖transportCommutator ((mollifierBump mollifierIndex).normed volume)
        (biotSavart (sequence index time)) (sequence index time) position‖) ∂timeMeasure) atTop (𝓝 0) := by
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.2.1
  obtain ⟨bound, boundNonnegative, bounded⟩ :=
    hypotheses.uniform_integral_transportCommutator_mollifier_norm horizonNonnegative
  have zeroIntegral : (∫ _ : Icc (0 : ℝ) horizon, (0 : ℝ) ∂timeMeasure) = 0 := by simp
  conv_rhs => rw [← zeroIntegral]
  apply tendsto_integral_of_dominated_convergence (fun _ => bound)
  · intro mollifierIndex
    exact (hypotheses.measurable_transportCommutator horizonNonnegative index
      ((mollifierBump (Space := Plane) mollifierIndex).contDiff_normed (μ := volume))
      ((mollifierBump (Space := Plane) mollifierIndex).hasCompactSupport_normed (μ := volume))).norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  · exact integrable_const bound
  · intro mollifierIndex
    exact Filter.Eventually.of_forall fun time => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (bounded index mollifierIndex time).2
  · filter_upwards [] with time
    exact EulerNonuniqueness.tendsto_integral_transportCommutator_mollifier_norm radiusPositive.le
      (fun exponent bound => ((hypotheses.2.2 index).2.2.2 exponent bound time time.property).1)
      (supported index time time.property) ((hypotheses.2.2 index).2.2.1 time time.property).2

theorem LocalCompactnessHypotheses.tendsto_setIntegral_transportCommutator_mollifier_norm
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (index : ℕ) :
    Tendsto (fun mollifierIndex => ∫ time in Icc (0 : ℝ) horizon, (∫ position : Plane,
      ‖transportCommutator ((mollifierBump mollifierIndex).normed volume)
        (biotSavart (sequence index time)) (sequence index time) position‖)) atTop (𝓝 0) := by
  letI : IsFiniteMeasure (volume : Measure (Icc (0 : ℝ) horizon)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  have result := hypotheses.tendsto_integral_transportCommutator_mollifier_norm
    horizonNonnegative (volume : Measure (Icc (0 : ℝ) horizon)) index
  apply result.congr'
  filter_upwards [] with mollifierIndex
  exact integral_subtype (s := Icc (0 : ℝ) horizon) measurableSet_Icc
    (fun time => ∫ position : Plane,
      ‖transportCommutator ((mollifierBump mollifierIndex).normed volume)
        (biotSavart (sequence index time)) (sequence index time) position‖)

end EulerNonuniqueness
