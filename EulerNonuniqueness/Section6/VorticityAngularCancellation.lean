import EulerNonuniqueness.Section6.VorticitySelfInteraction

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem integrable_vorticity_angular_pair {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius bound : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (bounded : ∀ position, |vorticity position| ≤ bound) (center : ℂ) :
    Integrable (fun pair : ℂ × ℂ => @inner ℝ ℂ _ (pair.1 - center)
      (vorticity pair.1 • (vorticity pair.2 • biotSavartKernel (pair.1 - pair.2))))
      (volume.prod volume) := by
  have joint := integrable_vorticity_pair_kernel integrable supported bounded
  apply (joint.norm.const_mul (radius + ‖center‖)).mono'
    (((continuous_fst.sub continuous_const).aestronglyMeasurable).inner joint.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun pair => by
    by_cases firstZero : vorticity pair.1 = 0
    · simp only [firstZero, zero_smul, inner_zero_right, norm_zero, mul_zero]
      exact le_rfl
    have firstBound : ‖pair.1‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using supported (Function.mem_support.mpr firstZero)
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((norm_sub_le _ _).trans (add_le_add_right firstBound _)) (norm_nonneg _))

theorem vorticity_angular_pair_antisymmetric (vorticity : Vorticity) (center first second : ℂ) :
    @inner ℝ ℂ _ (first - center)
      (vorticity first • (vorticity second • biotSavartKernel (first - second))) =
    -(@inner ℝ ℂ _ (second - center)
      (vorticity second • (vorticity first • biotSavartKernel (second - first)))) := by
  have cancellation : @inner ℝ ℂ _ (first - center) (biotSavartKernel (first - second)) -
      @inner ℝ ℂ _ (second - center) (biotSavartKernel (first - second)) = 0 := by
    rw [← inner_sub_left, show (first - center) - (second - center) = first - second by abel]
    exact real_inner_biotSavartKernel (first - second)
  simp only [show second - first = -(first - second) by abel, biotSavartKernel_neg,
    real_inner_smul_right, inner_neg_right]
  linear_combination (vorticity first * vorticity second) * cancellation

theorem integral_vorticity_angular_pair {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius bound : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (bounded : ∀ position, |vorticity position| ≤ bound) (center : ℂ) :
    (∫ first : ℂ, ∫ second : ℂ, @inner ℝ ℂ _ (first - center)
      (vorticity first • (vorticity second • biotSavartKernel (first - second)))) = 0 := by
  have joint := integrable_vorticity_angular_pair integrable supported bounded center
  have swapped := integral_integral_swap (μ := volume) (ν := volume)
    (f := fun first second : ℂ => @inner ℝ ℂ _ (first - center)
      (vorticity first • (vorticity second • biotSavartKernel (first - second)))) joint
  have opposite : (∫ first : ℂ, ∫ second : ℂ, @inner ℝ ℂ _ (first - center)
      (vorticity first • (vorticity second • biotSavartKernel (first - second)))) =
      -(∫ first : ℂ, ∫ second : ℂ, @inner ℝ ℂ _ (second - center)
        (vorticity second • (vorticity first • biotSavartKernel (second - first)))) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with first
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun second =>
      vorticity_angular_pair_antisymmetric vorticity center first second)
  rw [← swapped] at opposite
  linarith

theorem integrable_vorticity_angular_self_interaction {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius bound : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (bounded : ∀ position, |vorticity position| ≤ bound) (center : ℂ) :
    Integrable (fun position => @inner ℝ ℂ _ (position - center)
      (vorticity position • biotSavart vorticity position)) := by
  have joint := integrable_vorticity_pair_kernel integrable supported bounded
  have angularJoint := integrable_vorticity_angular_pair integrable supported bounded center
  apply angularJoint.integral_prod_left.congr
  filter_upwards [joint.prod_right_ae] with position sectionIntegrable
  rw [integral_inner sectionIntegrable]
  simp only [biotSavart, integral_smul]

theorem integral_vorticity_angular_self_interaction {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius bound : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (bounded : ∀ position, |vorticity position| ≤ bound) (center : ℂ) :
    (∫ position, @inner ℝ ℂ _ (position - center)
      (vorticity position • biotSavart vorticity position)) = 0 := by
  have joint := integrable_vorticity_pair_kernel integrable supported bounded
  rw [← integral_vorticity_angular_pair integrable supported bounded center]
  apply integral_congr_ae
  filter_upwards [joint.prod_right_ae] with position sectionIntegrable
  rw [integral_inner sectionIntegrable]
  simp only [biotSavart, integral_smul]

end EulerNonuniqueness.Section6
