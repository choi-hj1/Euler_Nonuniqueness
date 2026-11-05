import EulerNonuniqueness.Section8.RegularizedAdvectionVelocity

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness.RegularizedFlowOn

theorem norm_moment_sub_le {source : Vorticity} {integrable : Integrable source}
    {scale horizon : ℝ} {positive : 0 < scale}
    (flow : RegularizedFlowOn source integrable scale positive horizon)
    (nonnegative : 0 ≤ horizon) (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    {test : Plane → ℝ} (smooth : ContDiff ℝ 1 test) (compact : HasCompactSupport test)
    {derivativeBound : ℝ} (boundNonnegative : 0 ≤ derivativeBound)
    (bounded : ∀ position, ‖fderiv ℝ test position‖ ≤ derivativeBound)
    {first second : ℝ} (firstInside : first ∈ Icc 0 horizon) (secondInside : second ∈ Icc 0 horizon) :
    ‖(∫ position, flow.vorticity second position * test position) -
      (∫ position, flow.vorticity first position * test position)‖ ≤
        (∫ label, ‖source label‖) * derivativeBound * regularizedSourceSpeed source * ‖second - first‖ := by
  have trajectoryEstimate (label : Plane) :
      ‖test (flow.particleMap second label) - test (flow.particleMap first label)‖ ≤
        (derivativeBound * regularizedSourceSpeed source) * ‖second - first‖ := by
    apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun time inside => (smooth.differentiable le_rfl _).hasFDerivAt.comp_hasDerivWithinAt time
        (flow.hasDerivWithinAt_particleTrajectory inside label))
      (fun time inside => ?_) (convex_Icc (0 : ℝ) horizon) firstInside secondInside
    exact ((fderiv ℝ test (flow.particleMap time label)).le_opNorm _).trans
      (mul_le_mul (bounded _) (flow.norm_lagrangianVelocity_le_sourceSpeed nonnegative membership inside _)
        (norm_nonneg _) boundNonnegative)
  obtain ⟨valueBound, valueBounded⟩ := compact.exists_bound_of_continuous smooth.continuous
  have integrandIntegrable (time : ℝ) : Integrable (fun label => source label * test (flow.particleMap time label)) := by
    have testContinuous : Continuous (fun label => test (flow.particleMap time label)) :=
      smooth.continuous.comp (flow.continuous_particleMap time)
    apply (integrable.norm.mul_const valueBound).mono'
      (integrable.aestronglyMeasurable.mul testContinuous.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun label => by
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul_of_nonneg_left (valueBounded _) (norm_nonneg _)
  have pullback (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      (∫ position, flow.vorticity time position * test position) =
        ∫ label, source label * test (flow.particleMap time label) := by
    simpa only [smul_eq_mul] using flow.integral_vorticity_smul nonnegative inside test
  rw [pullback second secondInside, pullback first firstInside,
    ← integral_sub (integrandIntegrable second) (integrandIntegrable first)]
  calc
    _ ≤ ∫ label, ‖source label‖ *
        ((derivativeBound * regularizedSourceSpeed source) * ‖second - first‖) :=
      norm_integral_le_of_norm_le (integrable.norm.mul_const _) (Filter.Eventually.of_forall fun label => by
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_left (trajectoryEstimate label) (norm_nonneg _))
    _ = _ := by rw [integral_mul_const]; ring

end EulerNonuniqueness.RegularizedFlowOn
