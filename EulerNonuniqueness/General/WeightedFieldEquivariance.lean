import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem weighted_field_derivative_intertwines (function : Space → Space)
    (input output weight : Space →L[ℝ] Space) (base : Space)
    (fixed : input base = base) (differentiable : DifferentiableAt ℝ function base)
    (equivariant : (fun current => output (function current)) =ᶠ[𝓝 base]
      (fun current => weight (function (input current)))) :
    output.comp (fderiv ℝ function base) =
      weight.comp ((fderiv ℝ function base).comp input) := by
  have transformed : HasFDerivAt function (fderiv ℝ function base) (input base) := by
    rw [fixed]
    exact differentiable.hasFDerivAt
  have first := output.hasFDerivAt.comp base differentiable.hasFDerivAt
  have second := weight.hasFDerivAt.comp base (transformed.comp base input.hasFDerivAt)
  exact first.unique (second.congr_of_eventuallyEq equivariant)

end

end EulerNonuniqueness.General
