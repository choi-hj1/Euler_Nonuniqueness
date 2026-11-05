import EulerNonuniqueness.Section8.Compactness
import EulerNonuniqueness.General.ConvolutionBounds

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace EulerNonuniqueness

theorem convolution_bound_of_biotSavart_domination {kernel : Velocity}
    (measurable : AEStronglyMeasurable kernel volume)
    (dominated : ∀ position, ‖kernel position‖ ≤ ‖biotSavartKernel position‖)
    {vorticity : Vorticity} (integrable : Integrable vorticity)
    (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume) (position : Plane) :
    Integrable (fun source => vorticity source • kernel (position - source)) ∧
      ‖∫ source, vorticity source • kernel (position - source)‖ ≤
        (eLpNorm vorticity (ENNReal.ofReal (4 : ℝ)) volume).toReal *
          (eLpNorm ((Metric.ball (0 : Plane) 1).indicator biotSavartKernel)
            (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
              (∫ source, ‖vorticity source‖) * (1 / (2 * Real.pi)) := by
  let near : Velocity := (Metric.ball (0 : Plane) 1).indicator kernel
  let far : Velocity := (Metric.ball (0 : Plane) 1)ᶜ.indicator kernel
  have kernelNearMember : MemLp ((Metric.ball (0 : Plane) 1).indicator biotSavartKernel)
      (ENNReal.ofReal (4 / 3 : ℝ)) volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr
      (memLp_biotSavartKernel_ball (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num) (by norm_num))
  have nearDominated : ∀ᵐ point ∂(volume : Measure Plane),
      ‖near point‖ ≤ ‖(Metric.ball (0 : Plane) 1).indicator biotSavartKernel point‖ :=
    Filter.Eventually.of_forall fun point => by
      by_cases inside : point ∈ Metric.ball (0 : Plane) 1
      · simpa only [near, indicator_of_mem inside] using dominated point
      · simp only [near, indicator_of_not_mem inside, norm_zero, le_refl]
  have nearMember : MemLp near (ENNReal.ofReal (4 / 3 : ℝ)) volume :=
    kernelNearMember.mono (measurable.indicator measurableSet_ball) nearDominated
  have nearNormBound : (eLpNorm near (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal ≤
      (eLpNorm ((Metric.ball (0 : Plane) 1).indicator biotSavartKernel)
        (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal :=
    ENNReal.toReal_mono kernelNearMember.eLpNorm_lt_top.ne (eLpNorm_mono_ae nearDominated)
  have farBound (point : Plane) : ‖far point‖ ≤ 1 / (2 * Real.pi) := by
    dsimp only [far]
    by_cases inside : point ∈ Metric.ball (0 : Plane) 1
    · rw [indicator_of_not_mem (not_mem_compl_iff.mpr inside), norm_zero]
      positivity
    · have radiusBound : 1 ≤ ‖point‖ := by
        simpa only [Metric.mem_ball, dist_zero_right, not_lt] using inside
      rw [indicator_of_mem inside]
      apply (dominated point).trans
      rw [norm_biotSavartKernel]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by nlinarith [Real.pi_pos])
  have nearIntegrable := integrable_convolution_smul_of_memLp holderConjugate_four_fourThirds
    membership nearMember position
  have farIntegrable := integrable_convolution_smul_of_bounded integrable
    (measurable.indicator measurableSet_ball.compl) farBound position
  have split : (fun source => vorticity source • kernel (position - source)) =
      fun source => vorticity source • near (position - source) +
        vorticity source • far (position - source) := by
    funext source
    by_cases inside : position - source ∈ Metric.ball (0 : Plane) 1 <;>
      simp only [near, far, indicator_of_mem, indicator_of_not_mem, inside,
        mem_compl_iff, not_true_eq_false, not_false_eq_true, smul_zero, add_zero, zero_add]
  rw [split]
  refine ⟨nearIntegrable.add farIntegrable, ?_⟩
  rw [integral_add nearIntegrable farIntegrable]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_convolution_smul_le_eLpNorm holderConjugate_four_fourThirds membership nearMember position).trans
      (mul_le_mul_of_nonneg_left nearNormBound ENNReal.toReal_nonneg)
  · exact norm_convolution_smul_le_of_bounded integrable farBound position

end EulerNonuniqueness
