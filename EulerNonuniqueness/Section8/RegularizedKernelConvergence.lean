import EulerNonuniqueness.Section8.RegularizedKernel
import EulerNonuniqueness.General.DominatedLpConvergence

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem tendsto_regularizedBiotSavartKernel {Index : Type*} {filter : Filter Index} {scales : Index → ℝ}
    (convergence : Tendsto scales filter (𝓝 0)) (position : Plane) :
    Tendsto (fun index => regularizedBiotSavartKernel (scales index) position) filter (𝓝 (biotSavartKernel position)) := by
  by_cases zero : position = 0
  · simpa only [zero, regularizedBiotSavartKernel_zero, biotSavartKernel, mul_zero, zero_div] using
      (tendsto_const_nhds (x := (0 : Plane)))
  have denominatorReal := (tendsto_const_nhds (x := (2 * Real.pi : ℝ))).mul
    ((tendsto_const_nhds (x := ‖position‖ ^ 2)).add (convergence.pow 2))
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at denominatorReal
  have denominatorComplex := Complex.continuous_ofReal.continuousAt.tendsto.comp denominatorReal
  have denominatorNonzero : ((2 * Real.pi * ‖position‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    positivity
  exact (tendsto_const_nhds (x := Complex.I * position)).div denominatorComplex denominatorNonzero

theorem tendsto_eLpNorm_regularizedKernel_sub {scales : ℕ → ℝ}
    (positive : ∀ index, 0 < scales index) (convergence : Tendsto scales atTop (𝓝 0))
    {measure : Measure Plane} {exponent : ℝ≥0∞} (exponentPositive : 0 < exponent)
    (exponentFinite : exponent ≠ ⊤) (kernelMember : MemLp biotSavartKernel exponent measure) :
    Tendsto (fun index => eLpNorm (regularizedBiotSavartKernel (scales index) - biotSavartKernel) exponent measure)
      atTop (𝓝 0) := by
  apply tendsto_eLpNorm_of_dominated_convergence exponentPositive exponentFinite
    (bound := fun position => ‖biotSavartKernel position‖)
  · exact fun index => (contDiff_regularizedBiotSavartKernel (positive index)).continuous.aestronglyMeasurable
  · exact kernelMember.norm
  · exact fun index => Filter.Eventually.of_forall fun position => by
      simpa only [norm_norm] using norm_regularizedBiotSavartKernel_le_kernel (positive index) position
  · exact Filter.Eventually.of_forall fun position => tendsto_regularizedBiotSavartKernel convergence position

end EulerNonuniqueness
