import EulerNonuniqueness.Section8.TransportTestCoefficient

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem uniform_transport_test_coefficient_L2_bounds
    {Index : Type*} {horizon : ℝ} {fields : Index → Evolution}
    (spatiallyContinuous : ∀ index, ∀ time ∈ Icc 0 horizon,
      Continuous (biotSavart (fields index time)))
    (uniformlyBounded : ∀ observationRadius : ℝ, 0 ≤ observationRadius →
      ∃ bound : ℝ≥0∞, bound < (⊤ : ℝ≥0∞) ∧ ∀ index, ∀ time ∈ Icc 0 horizon,
        ∀ position ∈ Metric.closedBall (0 : Plane) observationRadius,
          ENNReal.ofReal ‖biotSavart (fields index time) position‖ ≤ bound)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ index, ∀ time ∈ Icc 0 horizon,
      MemLp (fun position => transportTestCoefficient test (fields index) (time, position)) 2 volume ∧
      (eLpNorm (fun position => transportTestCoefficient test (fields index) (time, position)) 2 volume).toReal ≤ bound := by
  obtain ⟨radius, radiusPositive, supported⟩ := scalarTest_spatial_support compact
  obtain ⟨testBound, testNonnegative, testBounded⟩ := scalarTest_uniform_bounds smooth compact
  obtain ⟨velocityBound, velocityFinite, velocityBounded⟩ := uniformlyBounded radius radiusPositive.le
  let pointwiseBound := testBound + testBound * velocityBound.toReal
  have pointwiseNonnegative : 0 ≤ pointwiseBound := by dsimp [pointwiseBound]; positivity
  let dominator := (Metric.closedBall (0 : Plane) radius).indicator (fun _ => pointwiseBound)
  have dominatorMember : MemLp dominator 2 volume := memLp_indicator_const 2 measurableSet_closedBall _
    (Or.inr (isCompact_closedBall (0 : Plane) radius).measure_lt_top.ne)
  refine ⟨(eLpNorm dominator 2 volume).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro index time inside
  have coefficientContinuous : Continuous (fun position => transportTestCoefficient test (fields index) (time, position)) := by
    have derivativeContinuous : Continuous (fun position : Plane => fderiv ℝ test (time, position)) :=
      (smooth.continuous_fderiv (by simp)).comp ((continuous_const : Continuous fun _ : Plane => time).prodMk continuous_id)
    exact (derivativeContinuous.clm_apply continuous_const).add
      (derivativeContinuous.clm_apply (continuous_const.prodMk (spatiallyContinuous index time inside)))
  have normBound (position : Plane) :
      ‖transportTestCoefficient test (fields index) (time, position)‖ ≤ ‖dominator position‖ := by
    by_cases positionInside : position ∈ Metric.closedBall (0 : Plane) radius
    · have velocityEstimate := ENNReal.toReal_mono velocityFinite.ne
        (velocityBounded index time inside position positionInside)
      simp only [ENNReal.toReal_ofReal (norm_nonneg _)] at velocityEstimate
      have pointwise : ‖transportTestCoefficient test (fields index) (time, position)‖ ≤ pointwiseBound :=
        (norm_add_le _ _).trans (add_le_add (testBounded time position).2.1
          (((testBounded time position).2.2 _).trans
            (mul_le_mul_of_nonneg_left velocityEstimate testNonnegative)))
      simpa only [dominator, indicator_of_mem positionInside, Real.norm_eq_abs,
        abs_of_nonneg pointwiseNonnegative] using pointwise
    · simp only [transportTestCoefficient, (supported time position positionInside).2.1,
        (supported time position positionInside).2.2, add_zero, norm_zero,
        dominator, indicator_of_not_mem positionInside, le_refl]
  refine ⟨dominatorMember.mono coefficientContinuous.aestronglyMeasurable
    (Eventually.of_forall normBound), ?_⟩
  exact ENNReal.toReal_mono dominatorMember.eLpNorm_lt_top.ne
    (eLpNorm_mono_ae (Eventually.of_forall normBound))

end EulerNonuniqueness
