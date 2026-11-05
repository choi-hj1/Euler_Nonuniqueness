import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem fderiv_intertwines_of_equivariant (function : Space → Space)
    (transform : Space →L[ℝ] Space) (base : Space)
    (first : DifferentiableAt ℝ function base)
    (transformed : DifferentiableAt ℝ function (transform base))
    (equivariant : (fun current => function (transform current)) =ᶠ[𝓝 base]
      (fun current => transform (function current))) :
    (fderiv ℝ function (transform base)).comp transform = transform.comp (fderiv ℝ function base) := by
  have left := transformed.hasFDerivAt.comp base transform.hasFDerivAt
  have right := transform.hasFDerivAt.comp base first.hasFDerivAt
  exact left.unique (right.congr_of_eventuallyEq equivariant)

theorem derivative_operator_field_intertwines
    (field : Space → Space →L[ℝ] Space) (transform : Space →L[ℝ] Space)
    (base : Space) (second : Space →L[ℝ] Space →L[ℝ] Space)
    (fixed : transform base = base) (derivative : HasFDerivAt field second base)
    (equivariant : (fun current => (field (transform current)).comp transform) =ᶠ[𝓝 base]
      (fun current => transform.comp (field current))) (firstDirection secondDirection : Space) :
    second (transform firstDirection) (transform secondDirection) =
      transform (second firstDirection secondDirection) := by
  let rightComposition : (Space →L[ℝ] Space) →L[ℝ] Space →L[ℝ] Space :=
    (ContinuousLinearMap.compL ℝ Space Space Space).flip transform
  let leftComposition : (Space →L[ℝ] Space) →L[ℝ] Space →L[ℝ] Space :=
    (ContinuousLinearMap.compL ℝ Space Space Space) transform
  have atTransformed : HasFDerivAt field second (transform base) := by rw [fixed]; exact derivative
  have left := rightComposition.hasFDerivAt.comp base (atTransformed.comp base transform.hasFDerivAt)
  have right := leftComposition.hasFDerivAt.comp base derivative
  have equality : (fun current => rightComposition (field (transform current))) =ᶠ[𝓝 base]
      (fun current => leftComposition (field current)) := equivariant
  have identity := left.unique (right.congr_of_eventuallyEq equality)
  exact congrArg (fun operator : Space →L[ℝ] Space →L[ℝ] Space =>
    operator firstDirection secondDirection) identity

end

end EulerNonuniqueness.General
