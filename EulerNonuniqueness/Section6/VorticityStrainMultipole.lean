import EulerNonuniqueness.Section6.CauchyStrainKernelMultipole
import EulerNonuniqueness.Section6.MovingExternalPatchDerivative

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem integrable_vorticity_smul_of_support_bound {vorticity : Vorticity}
    (integrable : Integrable vorticity) (function : ℂ → ℂ) (measurable : Measurable function)
    {bound : ℝ} (nonnegative : 0 ≤ bound)
    (bounded : ∀ source ∈ Function.support vorticity, ‖function source‖ ≤ bound) :
    Integrable (fun source => vorticity source • function source) := by
  have majorant : Integrable (fun source => bound * |vorticity source|) := integrable.norm.const_mul bound
  apply majorant.mono' (integrable.aestronglyMeasurable.smul measurable.aestronglyMeasurable)
  filter_upwards [] with source
  rw [norm_smul, Real.norm_eq_abs]
  by_cases zero : vorticity source = 0
  · simp only [zero, abs_zero, zero_mul, mul_zero, le_refl]
  · exact (mul_le_mul_of_nonneg_left (bounded source zero) (abs_nonneg _)).trans_eq (mul_comm _ _)

theorem vorticity_cauchy_strain_multipole_bound {vorticity : Vorticity}
    (integrable : Integrable vorticity) {center location : ℂ} {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius)
    (supported : Function.support vorticity ⊆ Metric.closedBall center radius)
    (locationPositive : 0 < ‖location - center‖) (separated : 2 * radius ≤ ‖location - center‖) :
    ‖(∫ source, vorticity source • (1 / (location - source) ^ 2 : ℂ)) -
        (∫ source, vorticity source • (1 : ℂ)) / (location - center) ^ 2 -
        2 * (∫ source, vorticity source • (source - center)) / (location - center) ^ 3 -
        3 * (∫ source, vorticity source • (source - center) ^ 2) / (location - center) ^ 4‖ ≤
      176 * radius ^ 3 * (∫ source, |vorticity source|) / ‖location - center‖ ^ 5 := by
  let displacement := location - center
  let remainder := fun source : ℂ => (1 / (location - source) ^ 2 : ℂ) - 1 / displacement ^ 2 -
    2 * (source - center) / displacement ^ 3 - 3 * (source - center) ^ 2 / displacement ^ 4
  have sourceBound (source : ℂ) (member : source ∈ Function.support vorticity) : ‖source - center‖ ≤ radius := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using supported member
  have kernelBound (source : ℂ) (member : source ∈ Function.support vorticity) :
      ‖(1 / (location - source) ^ 2 : ℂ)‖ ≤ 4 / ‖displacement‖ ^ 2 := by
    have triangle := norm_add_le (location - source) (source - center)
    rw [sub_add_sub_cancel] at triangle
    have half : ‖displacement‖ / 2 ≤ ‖location - source‖ := by
      dsimp only [displacement]
      linarith [sourceBound source member]
    rw [norm_div, norm_one, norm_pow]
    have bound := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : 0 < (‖displacement‖ / 2) ^ 2)
      (pow_le_pow_left₀ (by positivity : 0 ≤ ‖displacement‖ / 2) half 2)
    exact bound.trans_eq (by ring)
  have kernelIntegrable := integrable_vorticity_smul_of_support_bound integrable
    (fun source => (1 / (location - source) ^ 2 : ℂ)) (by fun_prop) (by positivity) kernelBound
  have massIntegrable := integrable_vorticity_smul_of_support_bound integrable (fun _ => (1 : ℂ)) measurable_const
    (show 0 ≤ (1 : ℝ) by norm_num) (fun _ _ => by simp)
  have firstIntegrable := integrable_vorticity_smul_of_support_bound integrable (fun source => source - center)
    (by fun_prop) radiusNonnegative sourceBound
  have secondIntegrable := integrable_vorticity_smul_of_support_bound integrable (fun source => (source - center) ^ 2)
    (by fun_prop) (sq_nonneg radius) (fun source member => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (sourceBound source member) 2)
  have remainderMeasurable : Measurable remainder := by dsimp only [remainder]; fun_prop
  have remainderBound (source : ℂ) (member : source ∈ Function.support vorticity) :
      ‖remainder source‖ ≤ 176 * radius ^ 3 / ‖displacement‖ ^ 5 :=
    cauchyStrain_kernel_multipole_bound locationPositive (sourceBound source member) separated
  have remainderIntegrable := integrable_vorticity_smul_of_support_bound integrable remainder remainderMeasurable
    (by positivity) remainderBound
  have estimate := norm_integral_le_of_norm_le
    (f := fun source => vorticity source • remainder source)
    (g := fun source => (176 * radius ^ 3 / ‖displacement‖ ^ 5) * |vorticity source|)
    (integrable.norm.const_mul _) (by
      filter_upwards [] with source
      rw [norm_smul, Real.norm_eq_abs]
      by_cases zero : vorticity source = 0
      · simp only [zero, abs_zero, zero_mul, mul_zero, le_refl]
      · exact (mul_le_mul_of_nonneg_left (remainderBound source zero) (abs_nonneg _)).trans_eq (mul_comm _ _))
  have pointwise : (fun source => vorticity source • remainder source) = fun source =>
      vorticity source • (1 / (location - source) ^ 2 : ℂ) -
        (vorticity source • (1 : ℂ)) / displacement ^ 2 -
        2 * (vorticity source • (source - center)) / displacement ^ 3 -
        3 * (vorticity source • (source - center) ^ 2) / displacement ^ 4 := by
    funext source
    simp only [remainder, Complex.real_smul]
    ring
  have massTermIntegrable := massIntegrable.div_const (displacement ^ 2)
  have firstTermIntegrable := (firstIntegrable.const_mul 2).div_const (displacement ^ 3)
  have secondTermIntegrable := (secondIntegrable.const_mul 3).div_const (displacement ^ 4)
  have firstExpansion :
      (∫ source, vorticity source • (1 / (location - source) ^ 2 : ℂ) -
        (vorticity source • (1 : ℂ)) / displacement ^ 2 -
        2 * (vorticity source • (source - center)) / displacement ^ 3) =
      (∫ source, vorticity source • (1 / (location - source) ^ 2 : ℂ) -
        (vorticity source • (1 : ℂ)) / displacement ^ 2) -
      (∫ source, 2 * (vorticity source • (source - center)) / displacement ^ 3) :=
    integral_sub (kernelIntegrable.sub massTermIntegrable) firstTermIntegrable
  have massExpansion :
      (∫ source, vorticity source • (1 / (location - source) ^ 2 : ℂ) -
        (vorticity source • (1 : ℂ)) / displacement ^ 2) =
      (∫ source, vorticity source • (1 / (location - source) ^ 2 : ℂ)) -
        (∫ source, (vorticity source • (1 : ℂ)) / displacement ^ 2) :=
    integral_sub kernelIntegrable massTermIntegrable
  have expansion : (∫ source, vorticity source • remainder source) =
      (∫ source, vorticity source • (1 / (location - source) ^ 2 : ℂ)) -
        (∫ source, vorticity source • (1 : ℂ)) / displacement ^ 2 -
        2 * (∫ source, vorticity source • (source - center)) / displacement ^ 3 -
        3 * (∫ source, vorticity source • (source - center) ^ 2) / displacement ^ 4 := by
    rw [pointwise]
    calc
      _ = (∫ source, vorticity source • (1 / (location - source) ^ 2 : ℂ) -
          (vorticity source • (1 : ℂ)) / displacement ^ 2 -
          2 * (vorticity source • (source - center)) / displacement ^ 3) -
          (∫ source, 3 * (vorticity source • (source - center) ^ 2) / displacement ^ 4) :=
        integral_sub ((kernelIntegrable.sub massTermIntegrable).sub firstTermIntegrable) secondTermIntegrable
      _ = _ := by
        rw [firstExpansion, massExpansion]
        simp only [integral_div, integral_const_mul]
  rw [expansion, integral_const_mul] at estimate
  exact estimate.trans_eq (by dsimp only [displacement]; ring)

end EulerNonuniqueness.Section6
