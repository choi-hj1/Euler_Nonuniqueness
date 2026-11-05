import EulerNonuniqueness.General.ComplexCubicProjectionRegularity
import EulerNonuniqueness.General.FiniteSpectralHomological

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]

theorem complexCubicHomologicalSolver_contDiff (eigenvalue : Fin 3 → ℂ) (frequency : ℂ) :
    ContDiff ℂ 1 (fun data : (Space →L[ℂ] Space) × (Space →L[ℂ] Space) =>
      finiteSpectralHomologicalSolver (complexCubicProjection data.1) eigenvalue frequency data.2) := by
  have projectionSmooth (branch : Fin 3) :
      ContDiff ℂ 1 (fun data : (Space →L[ℂ] Space) × (Space →L[ℂ] Space) => complexCubicProjection data.1 branch) :=
    (complexCubicProjection_contDiff branch).comp contDiff_fst
  unfold finiteSpectralHomologicalSolver
  apply ContDiff.sum
  intro output _
  apply ContDiff.sum
  intro input _
  exact ((projectionSmooth output).clm_comp (contDiff_snd.clm_comp (projectionSmooth input))).const_smul
    ((frequency + eigenvalue input - eigenvalue output)⁻¹)

end EulerNonuniqueness.General
