import EulerNonuniqueness.Section8.RegularizedTransportIntegrability

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness.RegularizedFlowOn

variable {source : Vorticity} {integrable : Integrable source}
  {scale horizon : ℝ} {positive : 0 < scale}
  (flow : RegularizedFlowOn source integrable scale positive horizon)

theorem integrable_lagrangian_transport (nonnegative : 0 ≤ horizon)
    (sourceMeasurable : Measurable source)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun point : ℝ × Plane => source point.2 *
      (timeDerivative test (point.1, flow.particleMap point.1 point.2) +
        spatialDerivative test (point.1, flow.particleMap point.1 point.2)
          (regularizedBiotSavart scale (flow.vorticity point.1) (flow.particleMap point.1 point.2))))
      (spacetimeMeasure horizon) := by
  obtain ⟨testBound, testBoundNonnegative, testBounded⟩ := scalarTest_uniform_bounds smooth compact
  let velocityBound : ℝ := regularizedKernelNormBound positive * sourceL1Mass source
  let coefficientBound := testBound + testBound * velocityBound
  have coefficientContinuous := (flow.continuous_transportCoefficient_on_time_subtype nonnegative
    (smooth.of_le (by simp))).comp
      (continuous_fst.prodMk flow.continuous_particleMap_on_time_subtype)
  have measurable := aestronglyMeasurable_spacetime_of_measurable_Icc nonnegative
    (field := fun point : ℝ × Plane => source point.2 *
      (timeDerivative test (point.1, flow.particleMap point.1 point.2) +
        spatialDerivative test (point.1, flow.particleMap point.1 point.2)
          (regularizedBiotSavart scale (flow.vorticity point.1) (flow.particleMap point.1 point.2))))
    ((sourceMeasurable.comp measurable_snd).mul coefficientContinuous.measurable)
  have temporalIntegrable : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo 0 horizon)) := integrable_const _
  have dominator : Integrable (fun point : ℝ × Plane => ‖source point.2‖ * coefficientBound)
      (spacetimeMeasure horizon) := by
    simpa only [one_mul] using temporalIntegrable.mul_prod (integrable.norm.mul_const coefficientBound)
  apply dominator.mono' measurable
  have timeInside : ∀ᵐ point ∂spacetimeMeasure horizon, point.1 ∈ Ioo 0 horizon :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [timeInside] with point inside
  have velocityEstimate := flow.norm_regularizedVelocity_le_crude nonnegative ⟨inside.1.le, inside.2.le⟩
    (flow.particleMap point.1 point.2)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (norm_add_le _ _).trans (add_le_add
    (testBounded point.1 (flow.particleMap point.1 point.2)).2.1
    (((testBounded point.1 (flow.particleMap point.1 point.2)).2.2 _).trans
      (mul_le_mul_of_nonneg_left velocityEstimate testBoundNonnegative)))

end EulerNonuniqueness.RegularizedFlowOn
