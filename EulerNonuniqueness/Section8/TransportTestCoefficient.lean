import EulerNonuniqueness.Section8.RegularizedMeasurability
import EulerNonuniqueness.Section8.TestBounds

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

def transportTestCoefficient (test : ℝ × Plane → ℝ) (omega : Evolution) (point : ℝ × Plane) : ℝ :=
  timeDerivative test point + spatialDerivative test point (biotSavart (omega point.1) point.2)

theorem transport_test_coefficient_properties_of_velocity_properties
    {horizon : ℝ} {omega : Evolution}
    (spatiallyContinuous : ∀ time ∈ Icc 0 horizon, Continuous (biotSavart (omega time)))
    (jointlyMeasurable : Measurable
      (fun point : Icc (0 : ℝ) horizon × Plane => biotSavart (omega point.1) point.2))
    (uniformlyBounded : ∀ observationRadius : ℝ, 0 ≤ observationRadius →
      ∃ bound : ℝ≥0∞, bound < (⊤ : ℝ≥0∞) ∧ ∀ time ∈ Icc 0 horizon,
        ∀ position ∈ Metric.closedBall (0 : Plane) observationRadius,
          ENNReal.ofReal ‖biotSavart (omega time) position‖ ≤ bound)
    (nonnegative : 0 ≤ horizon)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      AEStronglyMeasurable (transportTestCoefficient test omega) (spacetimeMeasure horizon) ∧
      Integrable (transportTestCoefficient test omega) (spacetimeMeasure horizon) ∧
      ∀ time ∈ Icc 0 horizon,
        MemLp (fun position => transportTestCoefficient test omega (time, position)) 2 volume ∧
        (eLpNorm (fun position => transportTestCoefficient test omega (time, position)) 2 volume).toReal ≤ bound := by
  obtain ⟨radius, positive, supported⟩ := scalarTest_spatial_support compact
  obtain ⟨testBound, testNonnegative, testBounded⟩ := scalarTest_uniform_bounds smooth compact
  obtain ⟨velocityBound, velocityFinite, velocityBounded⟩ := uniformlyBounded radius positive.le
  let pointwiseBound := testBound + testBound * velocityBound.toReal
  have pointwiseNonnegative : 0 ≤ pointwiseBound := by dsimp [pointwiseBound]; positivity
  have bounded (time : ℝ) (inside : time ∈ Icc 0 horizon) (position : Plane)
      (positionInside : position ∈ Metric.closedBall (0 : Plane) radius) :
      ‖transportTestCoefficient test omega (time, position)‖ ≤ pointwiseBound := by
    have velocityEstimate := ENNReal.toReal_mono velocityFinite.ne (velocityBounded time inside position positionInside)
    simp only [ENNReal.toReal_ofReal (norm_nonneg _)] at velocityEstimate
    exact (norm_add_le _ _).trans (add_le_add (testBounded time position).2.1
      (((testBounded time position).2.2 _).trans (mul_le_mul_of_nonneg_left velocityEstimate testNonnegative)))
  have vanishes (time : ℝ) (position : Plane) (outside : position ∉ Metric.closedBall (0 : Plane) radius) :
      transportTestCoefficient test omega (time, position) = 0 := by
    simp only [transportTestCoefficient, (supported time position outside).2.1,
      (supported time position outside).2.2, add_zero]
  have velocityMeasurable := aestronglyMeasurable_spacetime_of_measurable_Icc
    (field := fun point : ℝ × Plane => biotSavart (omega point.1) point.2) nonnegative jointlyMeasurable
  have temporalMeasurable : AEStronglyMeasurable (timeDerivative test) (spacetimeMeasure horizon) :=
    ((smooth.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
  have spatialMeasurable : AEStronglyMeasurable
      (fun point : ℝ × Plane => spatialDerivative test point (biotSavart (omega point.1) point.2)) (spacetimeMeasure horizon) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((smooth.continuous_fderiv (by simp)).aestronglyMeasurable.prodMk
        (aestronglyMeasurable_const.prodMk velocityMeasurable))
  have measurable : AEStronglyMeasurable (transportTestCoefficient test omega) (spacetimeMeasure horizon) :=
    temporalMeasurable.add spatialMeasurable
  have integrable : Integrable (transportTestCoefficient test omega) (spacetimeMeasure horizon) :=
    integrable_spacetime_of_supported_bounded measurable
      (fun time inside => bounded time ⟨inside.1.le, inside.2.le⟩)
      (fun time _ position outside => vanishes time position outside)
  let dominator := (Metric.closedBall (0 : Plane) radius).indicator (fun _ => pointwiseBound)
  have dominatorMember : MemLp dominator 2 volume := memLp_indicator_const 2 measurableSet_closedBall _
    (Or.inr (isCompact_closedBall (0 : Plane) radius).measure_lt_top.ne)
  refine ⟨(eLpNorm dominator 2 volume).toReal, ENNReal.toReal_nonneg, measurable, integrable, ?_⟩
  intro time inside
  have coefficientContinuous : Continuous (fun position => transportTestCoefficient test omega (time, position)) := by
    have derivativeContinuous : Continuous (fun position : Plane => fderiv ℝ test (time, position)) :=
      (smooth.continuous_fderiv (by simp)).comp ((continuous_const : Continuous fun _ : Plane => time).prodMk continuous_id)
    exact (derivativeContinuous.clm_apply continuous_const).add
      (derivativeContinuous.clm_apply (continuous_const.prodMk (spatiallyContinuous time inside)))
  have normBound : ∀ position, ‖transportTestCoefficient test omega (time, position)‖ ≤ ‖dominator position‖ := by
    intro position
    by_cases positionInside : position ∈ Metric.closedBall (0 : Plane) radius
    · simpa only [dominator, indicator_of_mem positionInside, Real.norm_eq_abs, abs_of_nonneg pointwiseNonnegative]
        using bounded time inside position positionInside
    · simp only [vanishes time position positionInside, norm_zero, dominator, indicator_of_not_mem positionInside, le_refl]
  refine ⟨dominatorMember.mono coefficientContinuous.aestronglyMeasurable (Filter.Eventually.of_forall normBound), ?_⟩
  exact ENNReal.toReal_mono dominatorMember.eLpNorm_lt_top.ne (eLpNorm_mono_ae (Filter.Eventually.of_forall normBound))

theorem TransportAnalyticHypotheses.transport_test_coefficient_properties
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      AEStronglyMeasurable (transportTestCoefficient test omega) (spacetimeMeasure horizon) ∧
      Integrable (transportTestCoefficient test omega) (spacetimeMeasure horizon) ∧
      ∀ time ∈ Icc 0 horizon,
        MemLp (fun position => transportTestCoefficient test omega (time, position)) 2 volume ∧
        (eLpNorm (fun position => transportTestCoefficient test omega (time, position)) 2 volume).toReal ≤ bound :=
  transport_test_coefficient_properties_of_velocity_properties
    (fun time inside => hypotheses.continuous_biotSavart inside)
    hypotheses.measurable_biotSavart
    (fun _ nonnegative => hypotheses.uniform_biotSavart_bound_on_closedBall nonnegative)
    nonnegative smooth compact

end EulerNonuniqueness
