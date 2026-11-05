import EulerNonuniqueness.Section8.RegularizedTransportDefectMeasurability

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem exists_regularizedTransportDefect_bound {source : Vorticity}
    (integrable : Integrable source) {horizon : ℝ} (nonnegative : 0 ≤ horizon)
    (sourceMeasurable : Measurable source) (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    {sourceBound : ℝ} (sourceBoundNonnegative : 0 ≤ sourceBound)
    (sourceBounded : ∀ position, ‖source position‖ ≤ sourceBound)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ index,
      Integrable (regularizedTransportDefect integrable nonnegative test index) (spacetimeMeasure horizon) ∧
      ‖∫ point, regularizedTransportDefect integrable nonnegative test index point ∂spacetimeMeasure horizon‖ ≤
        constant * regularizedDefectBound source index := by
  obtain ⟨testBound, testBoundNonnegative, testBounded⟩ := scalarTest_uniform_bounds smooth compact
  obtain ⟨radius, _, outside⟩ := scalarTest_spatial_support compact
  let dominator := fun point : ℝ × Plane =>
    (Metric.closedBall (0 : Plane) radius).indicator (fun _ => sourceBound * testBound) point.2
  have spatialIntegrable : Integrable
      ((Metric.closedBall (0 : Plane) radius).indicator (fun _ => sourceBound * testBound)) volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const.mpr (Or.inr (isCompact_closedBall (0 : Plane) radius).measure_lt_top))
  have temporalIntegrable : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo 0 horizon)) := integrable_const _
  have dominatorIntegrable : Integrable dominator (spacetimeMeasure horizon) := by
    simpa only [one_mul] using temporalIntegrable.mul_prod spatialIntegrable
  have dominatorNonnegative (point : ℝ × Plane) : 0 ≤ dominator point := by
    dsimp only [dominator]
    by_cases inside : point.2 ∈ Metric.closedBall (0 : Plane) radius
    · simpa only [indicator_of_mem inside] using mul_nonneg sourceBoundNonnegative testBoundNonnegative
    · simp only [indicator_of_not_mem inside, le_refl]
  refine ⟨∫ point, dominator point ∂spacetimeMeasure horizon, integral_nonneg dominatorNonnegative, ?_⟩
  intro index
  let flow := regularizedApproximationFlow integrable nonnegative index
  have measurable := aestronglyMeasurable_regularizedTransportDefect integrable nonnegative sourceMeasurable smooth index
  have pointwise : ∀ᵐ point ∂spacetimeMeasure horizon,
      ‖regularizedTransportDefect integrable nonnegative test index point‖ ≤ dominator point * regularizedDefectBound source index := by
    have timeInside : ∀ᵐ point ∂spacetimeMeasure horizon, point.1 ∈ Ioo 0 horizon :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
    filter_upwards [timeInside] with point inside
    have timeClosed : point.1 ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
    by_cases positionInside : point.2 ∈ Metric.closedBall (0 : Plane) radius
    · have sourceEstimate : ‖regularizedApproximation integrable nonnegative index point.1 point.2‖ ≤ sourceBound :=
        norm_injectionAdvection_le (flow.injective_particleMap timeClosed)
          sourceBoundNonnegative sourceBounded point.2
      have velocityEstimate : ‖biotSavart (regularizedApproximation integrable nonnegative index point.1) point.2 -
          regularizedBiotSavart (regularizationScale index)
            (regularizedApproximation integrable nonnegative index point.1) point.2‖ ≤ regularizedDefectBound source index := by
        simpa only [norm_sub_rev] using norm_regularizedApproximation_velocity_defect_le
          integrable nonnegative membership index timeClosed point.2
      have coefficientEstimate := ((testBounded point.1 point.2).2.2
        (biotSavart (regularizedApproximation integrable nonnegative index point.1) point.2 -
          regularizedBiotSavart (regularizationScale index)
            (regularizedApproximation integrable nonnegative index point.1) point.2)).trans
              (mul_le_mul_of_nonneg_left velocityEstimate testBoundNonnegative)
      dsimp only [regularizedTransportDefect, dominator]
      rw [indicator_of_mem positionInside, norm_mul]
      exact (mul_le_mul sourceEstimate coefficientEstimate (norm_nonneg _) sourceBoundNonnegative).trans_eq (by ring)
    · simp only [regularizedTransportDefect, dominator, (outside point.1 point.2 positionInside).2.2,
        mul_zero, norm_zero, indicator_of_not_mem positionInside, zero_mul, le_refl]
  refine ⟨(dominatorIntegrable.mul_const _).mono' measurable pointwise, ?_⟩
  have estimate := norm_integral_le_of_norm_le (dominatorIntegrable.mul_const (regularizedDefectBound source index)) pointwise
  simpa only [integral_mul_const] using estimate

theorem tendsto_integral_regularizedTransportDefect {source : Vorticity}
    (integrable : Integrable source) {horizon : ℝ} (nonnegative : 0 ≤ horizon)
    (sourceMeasurable : Measurable source) (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    {sourceBound : ℝ} (sourceBoundNonnegative : 0 ≤ sourceBound)
    (sourceBounded : ∀ position, ‖source position‖ ≤ sourceBound)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Tendsto (fun index => ∫ point, regularizedTransportDefect integrable nonnegative test index point
      ∂spacetimeMeasure horizon) atTop (𝓝 0) := by
  obtain ⟨constant, _, bounded⟩ := exists_regularizedTransportDefect_bound integrable nonnegative sourceMeasurable
    membership sourceBoundNonnegative sourceBounded smooth compact
  apply squeeze_zero_norm (fun index => (bounded index).2)
  simpa only [mul_zero] using (tendsto_regularizedDefectBound source).const_mul constant

end EulerNonuniqueness
