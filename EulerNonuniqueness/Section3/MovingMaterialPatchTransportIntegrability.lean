import EulerNonuniqueness.Section3.MovingMaterialPatchFlux
import EulerNonuniqueness.Section3.FiniteLiteralPatchTestSlices

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

theorem integrable_passive_transport (path : MovingMaterialPatch) {horizon : ℝ}
    (source : ℝ → Vorticity)
    (velocityMeasurable : Measurable (fun point : ℝ × ℂ => biotSavart (source point.1) point.2))
    {speed : ℝ} (speedNonnegative : 0 ≤ speed)
    (speedBound : ∀ time ∈ Ioo 0 horizon, ∀ position, ‖biotSavart (source time) position‖ ≤ speed)
    {test : ℝ × ℂ → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun point : ℝ × ℂ => (path.domain point.1).indicator (fun _ => (1 : ℝ)) point.2 *
      (timeDerivative test point + spatialDerivative test point (biotSavart (source point.1) point.2)))
      (spacetimeMeasure horizon) := by
  obtain ⟨testBound, testBoundNonnegative, testBounded⟩ := scalarTest_uniform_bounds smooth compact
  obtain ⟨radius, _, outside⟩ := scalarTest_spatial_support compact
  have derivativeMeasurable := (smooth.continuous_fderiv (by simp)).aestronglyMeasurable
    (μ := spacetimeMeasure horizon)
  have temporalMeasurable : AEStronglyMeasurable (timeDerivative test) (spacetimeMeasure horizon) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (derivativeMeasurable.prodMk aestronglyMeasurable_const)
  have spatialMeasurable : AEStronglyMeasurable (fun point : ℝ × ℂ => spatialDerivative test point
      (biotSavart (source point.1) point.2)) (spacetimeMeasure horizon) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (derivativeMeasurable.prodMk (aestronglyMeasurable_const.prodMk velocityMeasurable.aestronglyMeasurable))
  apply integrable_spacetime_of_supported_bounded
    (path.measurable_domain_indicator.aestronglyMeasurable.mul (temporalMeasurable.add spatialMeasurable))
    (radius := radius) (bound := testBound + testBound * speed)
  · intro time inside position _
    have coefficientBound : ‖timeDerivative test (time, position) + spatialDerivative test (time, position)
        (biotSavart (source time) position)‖ ≤ testBound + testBound * speed :=
      (norm_add_le _ _).trans (add_le_add (testBounded time position).2.1
        (((testBounded time position).2.2 _).trans
          (mul_le_mul_of_nonneg_left (speedBound time inside position) testBoundNonnegative)))
    simp only [Pi.mul_apply, Pi.add_apply]
    by_cases member : position ∈ path.domain time
    · simpa only [indicator_of_mem member, one_mul] using coefficientBound
    · simp only [indicator_of_not_mem member, zero_mul, norm_zero]
      exact add_nonneg testBoundNonnegative (mul_nonneg testBoundNonnegative speedNonnegative)
  · intro time _ position notInside
    have vanishing := outside time position notInside
    simp only [Pi.mul_apply, Pi.add_apply, vanishing.2.1, vanishing.2.2, zero_add, mul_zero]

theorem domain_test_temporal_integrable (path : MovingMaterialPatch) (time : ℝ)
    {test : ℝ × ℂ → ℝ} (smooth : ContDiff ℝ ∞ test) :
    IntegrableOn (fun position => timeDerivative test (time, position)) (path.domain time) :=
  path.integral_continuous_function time
    (((smooth.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const)

theorem domain_test_spatial_integrable (path : MovingMaterialPatch) (time : ℝ)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    {test : ℝ × ℂ → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    IntegrableOn (fun position => spatialDerivative test (time, position) (biotSavart source position)) (path.domain time) := by
  obtain ⟨bound, nonnegative, bounded⟩ := scalarTest_uniform_bounds smooth compact
  have velocityIntegrable := Section6.integrableOn_biotSavart_of_L1_L4_finite sourceIntegrable sourceMembership
    (path.domain_isBounded time).measure_lt_top
  have derivativeMeasurable := ((smooth.continuous_fderiv (by simp)).comp
    (continuous_const.prodMk continuous_id : Continuous (fun position : ℂ => (time, position)))).aestronglyMeasurable
      (μ := volume.restrict (path.domain time))
  apply (velocityIntegrable.norm.const_mul bound).mono'
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (derivativeMeasurable.prodMk (aestronglyMeasurable_const.prodMk velocityIntegrable.aestronglyMeasurable)))
  exact Filter.Eventually.of_forall fun position => (bounded time position).2.2 _

end EulerNonuniqueness.Paper.MovingMaterialPatch
