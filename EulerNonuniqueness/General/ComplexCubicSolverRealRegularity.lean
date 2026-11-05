import EulerNonuniqueness.General.ComplexCubicSolverRegularity
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import EulerNonuniqueness.Section3.LocalLipschitzCalculus

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

local instance solverRealOperatorSpace : NormedSpace ℝ (Space →L[ℂ] Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℝ)
    (E := Space) (F := Space) (σ₁₂ := RingHom.id ℂ)

local instance solverOperatorTower : IsScalarTower ℝ ℂ (Space →L[ℂ] Space) :=
  ⟨fun scalar coefficient operator => by
    apply ContinuousLinearMap.ext
    intro vector
    exact smul_assoc scalar coefficient (operator vector)⟩

local instance solverTupleTower : IsScalarTower ℝ ℂ
    ((Space →L[ℂ] Space) × (Space →L[ℂ] Space)) :=
  ⟨fun scalar coefficient data => Prod.ext (smul_assoc scalar coefficient data.1)
    (smul_assoc scalar coefficient data.2)⟩

theorem complexCubicHomologicalSolver_real_contDiff (eigenvalue : Fin 3 → ℂ) (frequency : ℂ) :
    ContDiff ℝ 1 (fun data : (Space →L[ℂ] Space) × (Space →L[ℂ] Space) =>
      finiteSpectralHomologicalSolver (complexCubicProjection data.1) eigenvalue frequency data.2) :=
  (complexCubicHomologicalSolver_contDiff eigenvalue frequency).restrict_scalars ℝ

theorem complexCubicHomologicalSolver_lipschitzNear (eigenvalue : Fin 3 → ℂ) (frequency : ℂ)
    (point : (Space →L[ℂ] Space) × (Space →L[ℂ] Space)) :
    LipschitzNear (fun data : (Space →L[ℂ] Space) × (Space →L[ℂ] Space) =>
      finiteSpectralHomologicalSolver (complexCubicProjection data.1) eigenvalue frequency data.2) point :=
  lipschitzNear_of_contDiffAt_one
    ((complexCubicHomologicalSolver_real_contDiff eigenvalue frequency).contDiffAt (x := point))

end EulerNonuniqueness.General
