import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.RealDeriv

namespace EulerNonuniqueness.General

noncomputable section

variable {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G]

theorem differentiableAt_restrictScalars_family {family : D → E →L[ℂ] F} {point : D}
    (differentiable : DifferentiableAt ℝ family point) :
    DifferentiableAt ℝ (fun value => (family value).restrictScalars ℝ) point :=
  (ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).differentiableAt.comp point differentiable

theorem differentiableAt_bilinearRestrictScalars_family
    {family : D → E →L[ℂ] F →L[ℂ] G} {point : D}
    (differentiable : DifferentiableAt ℝ family point) :
    DifferentiableAt ℝ (fun value => (family value).bilinearRestrictScalars ℝ) point := by
  have restricted : DifferentiableAt ℝ (fun value => (family value).restrictScalars ℝ) point :=
    differentiableAt_restrictScalars_family differentiable
  have constant : DifferentiableAt ℝ (fun _ : D => ContinuousLinearMap.restrictScalarsL ℂ F G ℝ ℝ) point :=
    differentiableAt_const (𝕜 := ℝ) (E := D)
      (F := (F →L[ℂ] G) →L[ℝ] F →L[ℝ] G) (x := point)
      (ContinuousLinearMap.restrictScalarsL ℂ F G ℝ ℝ)
  exact DifferentiableAt.clm_comp (𝕜 := ℝ) (E := D) (F := E)
    (G := F →L[ℂ] G) (H := F →L[ℝ] G) constant restricted

end

end EulerNonuniqueness.General
