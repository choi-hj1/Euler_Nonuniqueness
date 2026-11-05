import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.NormedSpace.OperatorNorm.Prod

namespace EulerNonuniqueness.General

noncomputable section

variable {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem differentiableAt_clm_comp_const {family : D → F →L[ℝ] G} {point : D}
    (differentiable : DifferentiableAt ℝ family point) (operator : E →L[ℝ] F) :
    DifferentiableAt ℝ (fun value => (family value).comp operator) point := by
  have constant : DifferentiableAt ℝ (fun _ : D => operator) point :=
    differentiableAt_const (𝕜 := ℝ) (E := D) (F := E →L[ℝ] F) (x := point) operator
  exact DifferentiableAt.clm_comp (𝕜 := ℝ) (E := D) (F := E) (G := F) (H := G) differentiable constant

theorem differentiableAt_const_clm_comp {family : D → E →L[ℝ] F} {point : D}
    (operator : F →L[ℝ] G) (differentiable : DifferentiableAt ℝ family point) :
    DifferentiableAt ℝ (fun value => operator.comp (family value)) point := by
  have constant : DifferentiableAt ℝ (fun _ : D => operator) point :=
    differentiableAt_const (𝕜 := ℝ) (E := D) (F := F →L[ℝ] G) (x := point) operator
  exact DifferentiableAt.clm_comp (𝕜 := ℝ) (E := D) (F := E) (G := F) (H := G) constant differentiable

theorem differentiableAt_clm_prod {first : D → E →L[ℝ] F} {second : D → E →L[ℝ] G} {point : D}
    (first_differentiable : DifferentiableAt ℝ first point)
    (second_differentiable : DifferentiableAt ℝ second point) :
    DifferentiableAt ℝ (fun value => (first value).prod (second value)) point := by
  exact ((ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := E) (F := F) (G := G) ℝ).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt).comp
    point (first_differentiable.prodMk second_differentiable)

end

end EulerNonuniqueness.General
