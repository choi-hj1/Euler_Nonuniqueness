import EulerNonuniqueness.Section3.ClosedSubmoduleDerivative
import Mathlib.Analysis.Asymptotics.Lemmas

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closedSubmodule_quadratic_coefficient_mem
    (subspace : Submodule ℝ E) (closed : IsClosed (subspace : Set E))
    (function : ℝ → subspace) (linear quadratic : E) (linear_mem : linear ∈ subspace)
    (remainder : (fun parameter : ℝ => (function parameter : E) - (function 0 : E) -
      parameter • linear - parameter ^ 2 • quadratic) =o[𝓝[≠] 0]
      (fun parameter : ℝ => parameter ^ 2)) :
    quadratic ∈ subspace := by
  have limit := remainder.tendsto_inv_smul_nhds_zero
  have translated := limit.add_const quadratic
  simp only [zero_add] at translated
  have equality : (fun parameter : ℝ =>
      (parameter ^ 2)⁻¹ • ((function parameter : E) - (function 0 : E) -
        parameter • linear - parameter ^ 2 • quadratic) + quadratic) =ᶠ[𝓝[≠] 0]
      (fun parameter : ℝ =>
        (parameter ^ 2)⁻¹ • ((function parameter : E) - (function 0 : E) - parameter • linear)) := by
    filter_upwards [self_mem_nhdsWithin] with parameter nonzero
    have nonzero : parameter ≠ 0 := nonzero
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 nonzero), one_smul,
      sub_add_cancel]
  apply closed.mem_of_tendsto (translated.congr' equality)
  apply Eventually.of_forall
  intro parameter
  exact subspace.smul_mem _ (subspace.sub_mem
    (subspace.sub_mem (function parameter).property (function 0).property)
    (subspace.smul_mem parameter linear_mem))

end

end EulerNonuniqueness.Paper
