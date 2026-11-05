import EulerNonuniqueness.Section3.FiniteLiteralPatchTestSlices

open Set MeasureTheory
open scoped ContDiff

namespace EulerNonuniqueness.Paper

noncomputable section

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem measurable_domain_indicator_joint (flow : FiniteLiteralPatchFlow configuration) (index : Fin count) :
    Measurable (fun point : ℝ × ℂ => (flow.domain point.1 index).indicator (fun _ => (1 : ℝ)) point.2) :=
  measurable_affinePatchDomain_indicator_joint (configuration.center index) (configuration.radius_pos index)
    (fun time => flow.shape time index) ((continuous_apply index).comp flow.continuous)
    (fun time => (flow.nearby time index).trans_le (min_le_left _ _))

theorem integrable_passive_transport (flow : FiniteLiteralPatchFlow configuration) (horizon : ℝ) (index : Fin count)
    {test : ℝ × ℂ → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun point : ℝ × ℂ => (flow.domain point.1 index).indicator (fun _ => (1 : ℝ)) point.2 *
      (timeDerivative test point + spatialDerivative test point (biotSavart (flow.vorticity point.1) point.2)))
      (spacetimeMeasure horizon) := by
  obtain ⟨testBound, testBoundNonnegative, testBounded⟩ := scalarTest_uniform_bounds smooth compact
  obtain ⟨radius, _, outside⟩ := scalarTest_spatial_support compact
  have derivativeMeasurable := (smooth.continuous_fderiv (by simp)).aestronglyMeasurable
    (μ := spacetimeMeasure horizon)
  have temporalMeasurable : AEStronglyMeasurable (timeDerivative test) (spacetimeMeasure horizon) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (derivativeMeasurable.prodMk aestronglyMeasurable_const)
  have spatialMeasurable : AEStronglyMeasurable (fun point : ℝ × ℂ => spatialDerivative test point
      (biotSavart (flow.vorticity point.1) point.2)) (spacetimeMeasure horizon) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (derivativeMeasurable.prodMk (aestronglyMeasurable_const.prodMk flow.measurable_biotSavart_joint.aestronglyMeasurable))
  apply integrable_spacetime_of_supported_bounded
    ((flow.measurable_domain_indicator_joint index).aestronglyMeasurable.mul (temporalMeasurable.add spatialMeasurable))
    (radius := radius) (bound := testBound + testBound * flow.speedBound)
  · intro time _ position _
    have coefficient_bound : ‖timeDerivative test (time, position) + spatialDerivative test (time, position)
        (biotSavart (flow.vorticity time) position)‖ ≤ testBound + testBound * flow.speedBound :=
      (norm_add_le _ _).trans (add_le_add (testBounded time position).2.1
        (((testBounded time position).2.2 _).trans
          (mul_le_mul_of_nonneg_left (flow.norm_biotSavart_le_speedBound time position) testBoundNonnegative)))
    simp only [Pi.mul_apply, Pi.add_apply]
    by_cases member : position ∈ flow.domain time index
    · simpa only [indicator_of_mem member, one_mul] using coefficient_bound
    · simp only [indicator_of_not_mem member, zero_mul, norm_zero]
      exact add_nonneg testBoundNonnegative (mul_nonneg testBoundNonnegative flow.speedBound_nonneg)
  · intro time _ position notInside
    have vanishing := outside time position notInside
    simp only [Pi.mul_apply, Pi.add_apply, vanishing.2.1, vanishing.2.2, zero_add, mul_zero]

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
