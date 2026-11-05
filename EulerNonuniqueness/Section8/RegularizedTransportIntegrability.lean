import EulerNonuniqueness.Section8.RegularizedTransportCoefficient
import EulerNonuniqueness.Section8.SpacetimeMeasurability
import EulerNonuniqueness.General.InjectionAdvectionBounds

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness.RegularizedFlowOn

variable {source : Vorticity} {integrable : Integrable source}
  {scale horizon : ℝ} {positive : 0 < scale}
  (flow : RegularizedFlowOn source integrable scale positive horizon)

theorem integrable_transport_terms (nonnegative : 0 ≤ horizon)
    (sourceMeasurable : Measurable source) {sourceBound : ℝ} (sourceBoundNonnegative : 0 ≤ sourceBound)
    (sourceBounded : ∀ position, ‖source position‖ ≤ sourceBound)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun point : ℝ × Plane => flow.vorticity point.1 point.2 *
      (timeDerivative test point + spatialDerivative test point
        (regularizedBiotSavart scale (flow.vorticity point.1) point.2))) (spacetimeMeasure horizon) ∧
      Integrable (fun position => source position * test (0, position)) := by
  obtain ⟨testBound, testBoundNonnegative, testBounded⟩ := scalarTest_uniform_bounds smooth compact
  obtain ⟨radius, _, outside⟩ := scalarTest_spatial_support compact
  have sourceMeasurable' := aestronglyMeasurable_spacetime_of_measurable_Icc nonnegative
    (field := fun point : ℝ × Plane => flow.vorticity point.1 point.2)
    (flow.measurable_vorticity_on_time_subtype sourceMeasurable)
  have coefficientMeasurable := aestronglyMeasurable_spacetime_of_measurable_Icc nonnegative
    (field := fun point : ℝ × Plane => timeDerivative test point + spatialDerivative test point
      (regularizedBiotSavart scale (flow.vorticity point.1) point.2))
    (flow.continuous_transportCoefficient_on_time_subtype nonnegative (smooth.of_le (by simp))).measurable
  let velocityBound : ℝ := regularizedKernelNormBound positive * sourceL1Mass source
  constructor
  · apply integrable_spacetime_of_supported_bounded (sourceMeasurable'.mul coefficientMeasurable)
      (radius := radius) (bound := sourceBound * (testBound + testBound * velocityBound))
    · intro time inside position _
      have timeInside : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
      have sourceEstimate : ‖flow.vorticity time position‖ ≤ sourceBound :=
        norm_injectionAdvection_le (flow.injective_particleMap timeInside)
          sourceBoundNonnegative sourceBounded position
      have velocityEstimate := flow.norm_regularizedVelocity_le_crude nonnegative timeInside position
      have coefficientEstimate : ‖timeDerivative test (time, position) + spatialDerivative test (time, position)
          (regularizedBiotSavart scale (flow.vorticity time) position)‖ ≤ testBound + testBound * velocityBound :=
        (norm_add_le _ _).trans (add_le_add (testBounded time position).2.1
          (((testBounded time position).2.2 _).trans
            (mul_le_mul_of_nonneg_left velocityEstimate testBoundNonnegative)))
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul sourceEstimate coefficientEstimate (norm_nonneg _) sourceBoundNonnegative
    · intro time _ position notInside
      have vanishing := outside time position notInside
      simp only [Pi.mul_apply, vanishing.2.1, vanishing.2.2, zero_add, mul_zero]
  · have testContinuous : Continuous (fun position : Plane => test (0, position)) :=
      smooth.continuous.comp (continuous_const.prodMk continuous_id)
    apply (integrable.norm.mul_const testBound).mono'
      (integrable.aestronglyMeasurable.mul testContinuous.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun position => by
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul_of_nonneg_left (testBounded 0 position).1 (norm_nonneg _)

end EulerNonuniqueness.RegularizedFlowOn
