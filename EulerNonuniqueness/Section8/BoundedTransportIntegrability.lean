import EulerNonuniqueness.Section8.SpacetimeMeasurability
import EulerNonuniqueness.Section8.TestBounds

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem integrable_transport_test_of_bounded_fields {horizon : ℝ}
    {omega : Evolution} {velocity : ℝ → Velocity}
    (sourceMeasurable : AEStronglyMeasurable (Function.uncurry omega) (spacetimeMeasure horizon))
    (velocityMeasurable : AEStronglyMeasurable (Function.uncurry velocity) (spacetimeMeasure horizon))
    {sourceBound velocityBound : ℝ} (sourceBoundNonnegative : 0 ≤ sourceBound)
    (sourceBounded : ∀ time ∈ Ioo 0 horizon, ∀ position, ‖omega time position‖ ≤ sourceBound)
    (velocityBounded : ∀ time ∈ Ioo 0 horizon, ∀ position, ‖velocity time position‖ ≤ velocityBound)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun point : ℝ × Plane => omega point.1 point.2 *
      (timeDerivative test point + spatialDerivative test point (velocity point.1 point.2)))
      (spacetimeMeasure horizon) := by
  obtain ⟨testBound, testBoundNonnegative, testBounded⟩ := scalarTest_uniform_bounds smooth compact
  obtain ⟨radius, _, outside⟩ := scalarTest_spatial_support compact
  have derivativeMeasurable := (smooth.continuous_fderiv (by simp)).aestronglyMeasurable
    (μ := spacetimeMeasure horizon)
  have temporalMeasurable := ((smooth.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
    (μ := spacetimeMeasure horizon) (f := fun point => timeDerivative test point)
  have spatialMeasurable : AEStronglyMeasurable
      (fun point => spatialDerivative test point (velocity point.1 point.2)) (spacetimeMeasure horizon) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (derivativeMeasurable.prodMk (aestronglyMeasurable_const.prodMk velocityMeasurable))
  apply integrable_spacetime_of_supported_bounded
    (sourceMeasurable.mul (temporalMeasurable.add spatialMeasurable))
    (radius := radius) (bound := sourceBound * (testBound + testBound * velocityBound))
  · intro time inside position _
    have coefficientEstimate : ‖timeDerivative test (time, position) +
        spatialDerivative test (time, position) (velocity time position)‖ ≤ testBound + testBound * velocityBound :=
      (norm_add_le _ _).trans (add_le_add (testBounded time position).2.1
        (((testBounded time position).2.2 _).trans
          (mul_le_mul_of_nonneg_left (velocityBounded time inside position) testBoundNonnegative)))
    simp only [Pi.mul_apply, Function.uncurry_apply_pair, norm_mul]
    exact mul_le_mul (sourceBounded time inside position) coefficientEstimate (norm_nonneg _) sourceBoundNonnegative
  · intro time _ position notInside
    have vanishing := outside time position notInside
    simp only [Pi.mul_apply, Pi.add_apply, Function.uncurry_apply_pair, vanishing.2.1, vanishing.2.2, zero_add, mul_zero]

end EulerNonuniqueness
