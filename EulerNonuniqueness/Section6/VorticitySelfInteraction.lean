import EulerNonuniqueness.Section6.PatchSelfInteraction

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem integrable_vorticity_pair_kernel {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius bound : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (bounded : ∀ position, |vorticity position| ≤ bound) :
    Integrable (fun pair : ℂ × ℂ =>
      vorticity pair.1 • (vorticity pair.2 • biotSavartKernel (pair.1 - pair.2)))
      (volume.prod volume) := by
  let truncated := (Metric.ball (0 : ℂ) (2 * radius + 1)).indicator biotSavartKernel
  have truncatedIntegrable : Integrable truncated :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_biotSavartKernel_ball _)
  have joint := integrable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) truncatedIntegrable
  apply (joint.norm.const_mul bound).mono'
    (integrable.aestronglyMeasurable.fst.smul (integrable.aestronglyMeasurable.snd.smul
      ((measurable_biotSavartKernel.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable)))
  exact Filter.Eventually.of_forall fun pair => by
    by_cases firstZero : vorticity pair.1 = 0
    · simp only [firstZero, zero_smul, norm_zero]
      exact mul_nonneg ((abs_nonneg (vorticity 0)).trans (bounded 0)) (norm_nonneg _)
    by_cases secondZero : vorticity pair.2 = 0
    · simp [secondZero]
    have firstBound : ‖pair.1‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using supported (Function.mem_support.mpr firstZero)
    have secondBound : ‖pair.2‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using supported (Function.mem_support.mpr secondZero)
    have differenceInside : pair.1 - pair.2 ∈ Metric.ball (0 : ℂ) (2 * radius + 1) := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (norm_sub_le _ _).trans_lt (by linarith)
    change ‖vorticity pair.1 • (vorticity pair.2 • biotSavartKernel (pair.1 - pair.2))‖ ≤
      bound * ‖vorticity pair.2 • truncated (pair.1 - pair.2)‖
    rw [show truncated (pair.1 - pair.2) = biotSavartKernel (pair.1 - pair.2) from
      indicator_of_mem differenceInside _, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (bounded pair.1) (norm_nonneg _)

theorem integrable_vorticity_self_interaction {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius bound : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (bounded : ∀ position, |vorticity position| ≤ bound) :
    Integrable (fun position => vorticity position • biotSavart vorticity position) := by
  have joint := integrable_vorticity_pair_kernel integrable supported bounded
  simpa only [biotSavart, integral_smul] using joint.integral_prod_left

theorem integral_vorticity_self_interaction {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius bound : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (bounded : ∀ position, |vorticity position| ≤ bound) :
    (∫ position, vorticity position • biotSavart vorticity position) = 0 := by
  have joint := integrable_vorticity_pair_kernel integrable supported bounded
  have swapped := integral_integral_swap (μ := volume) (ν := volume)
    (f := fun first second : ℂ =>
      vorticity first • (vorticity second • biotSavartKernel (first - second))) joint
  have antisymmetric (first second : ℂ) :
      vorticity first • (vorticity second • biotSavartKernel (first - second)) =
        -(vorticity second • (vorticity first • biotSavartKernel (second - first))) := by
    rw [show second - first = -(first - second) by abel, biotSavartKernel_neg,
      smul_neg, smul_neg, neg_neg, smul_smul, smul_smul, mul_comm]
  have opposite : (∫ first : ℂ, ∫ second : ℂ,
      vorticity first • (vorticity second • biotSavartKernel (first - second))) =
      -(∫ first : ℂ, ∫ second : ℂ,
        vorticity second • (vorticity first • biotSavartKernel (second - first))) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with first
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun second => antisymmetric first second)
  have zero : (∫ first : ℂ, ∫ second : ℂ,
      vorticity first • (vorticity second • biotSavartKernel (first - second))) = 0 := by
    rw [← swapped] at opposite
    linear_combination (1 / 2 : ℂ) * opposite
  simpa only [biotSavart, integral_smul] using zero

theorem real_inner_biotSavartKernel (position : ℂ) :
    @Inner.inner ℝ ℂ _ position (biotSavartKernel position) = 0 := by
  rw [Complex.inner]
  simp only [biotSavartKernel, div_mul_eq_mul_div, mul_assoc, Complex.mul_conj]
  simp [Complex.div_re, Complex.mul_re, ← Complex.ofReal_pow]

end EulerNonuniqueness.Section6
