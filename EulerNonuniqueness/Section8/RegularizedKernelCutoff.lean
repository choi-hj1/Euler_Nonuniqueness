import EulerNonuniqueness.Section8.RegularizedKernelDifference

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace EulerNonuniqueness

def nearRegularizedKernelDifference (scale : ℝ) : Velocity :=
  (Metric.ball (0 : Plane) 1).indicator (regularizedBiotSavartKernel scale - biotSavartKernel)

def farRegularizedKernelDifference (scale : ℝ) : Velocity :=
  (Metric.ball (0 : Plane) 1)ᶜ.indicator (regularizedBiotSavartKernel scale - biotSavartKernel)

theorem nearRegularizedKernelDifference_memLp {scale exponent : ℝ} (positive : 0 < scale)
    (exponentPositive : 0 < exponent) (exponentBound : exponent < 2) :
    MemLp (nearRegularizedKernelDifference scale) (ENNReal.ofReal exponent) volume :=
  (memLp_indicator_iff_restrict measurableSet_ball).mpr
    (regularizedKernel_sub_memLp_ball positive exponentPositive exponentBound (by norm_num))

theorem measurable_farRegularizedKernelDifference {scale : ℝ} (positive : 0 < scale) :
    Measurable (farRegularizedKernelDifference scale) :=
  ((contDiff_regularizedBiotSavartKernel positive).continuous.measurable.sub
    measurable_biotSavartKernel).indicator measurableSet_ball.compl

theorem norm_farRegularizedKernelDifference_le {scale : ℝ} (positive : 0 < scale) (position : Plane) :
    ‖farRegularizedKernelDifference scale position‖ ≤ scale ^ 2 / (2 * Real.pi) := by
  by_cases inside : position ∈ Metric.ball (0 : Plane) 1
  · rw [farRegularizedKernelDifference, indicator_of_not_mem (not_mem_compl_iff.mpr inside), norm_zero]
    positivity
  · rw [farRegularizedKernelDifference, indicator_of_mem inside]
    exact norm_regularizedBiotSavartKernel_sub_le_far positive
      (by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using inside)

theorem near_add_far_regularizedKernelDifference (scale : ℝ) :
    nearRegularizedKernelDifference scale + farRegularizedKernelDifference scale =
      regularizedBiotSavartKernel scale - biotSavartKernel := by
  funext position
  by_cases inside : position ∈ Metric.ball (0 : Plane) 1 <;>
    simp only [Pi.add_apply, nearRegularizedKernelDifference, farRegularizedKernelDifference,
      indicator_of_mem, indicator_of_not_mem, inside, mem_compl_iff, not_true_eq_false,
      not_false_eq_true, add_zero, zero_add]

theorem tendsto_eLpNorm_nearRegularizedKernelDifference {scales : ℕ → ℝ}
    (positive : ∀ index, 0 < scales index) (convergence : Tendsto scales atTop (𝓝 0))
    {exponent : ℝ} (exponentPositive : 0 < exponent) (exponentBound : exponent < 2) :
    Tendsto (fun index => eLpNorm (nearRegularizedKernelDifference (scales index))
      (ENNReal.ofReal exponent) volume) atTop (𝓝 0) := by
  simp only [nearRegularizedKernelDifference, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
  exact tendsto_eLpNorm_regularizedKernel_sub_ball positive convergence exponentPositive exponentBound (by norm_num)

end EulerNonuniqueness
