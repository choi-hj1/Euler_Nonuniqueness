import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

open Filter Set
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem closedSubmodule_derivative_mem (subspace : Submodule ℝ F) (closed : IsClosed (subspace : Set F))
    {function : E → subspace} {derivative : E →L[ℝ] F} {point : E}
    (differentiable : HasFDerivAt (fun current => (function current : F)) derivative point) (direction : E) :
    derivative direction ∈ subspace := by
  have line : HasDerivAt (fun parameter : ℝ => (function (point + parameter • direction) : F))
      (derivative direction) 0 := differentiable.hasLineDerivAt direction
  apply closed.mem_of_tendsto line.tendsto_slope_zero
  apply Eventually.of_forall
  intro parameter
  exact subspace.smul_mem _ (subspace.sub_mem (function _).property (function _).property)

def closedSubmoduleDerivative (subspace : Submodule ℝ F) (closed : IsClosed (subspace : Set F))
    {function : E → subspace} {derivative : E →L[ℝ] F} {point : E}
    (differentiable : HasFDerivAt (fun current => (function current : F)) derivative point) : E →L[ℝ] subspace :=
  derivative.codRestrict subspace (closedSubmodule_derivative_mem subspace closed differentiable)

theorem hasFDerivAt_closedSubmodule (subspace : Submodule ℝ F) (closed : IsClosed (subspace : Set F))
    {function : E → subspace} {derivative : E →L[ℝ] F} {point : E}
    (differentiable : HasFDerivAt (fun current => (function current : F)) derivative point) :
    HasFDerivAt function (closedSubmoduleDerivative subspace closed differentiable) point := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  have ambient := hasFDerivAt_iff_isLittleO_nhds_zero.mp differentiable
  rw [Asymptotics.isLittleO_iff] at ambient ⊢
  intro epsilon positive
  filter_upwards [ambient positive] with increment bound
  exact bound

end

end EulerNonuniqueness.Paper
