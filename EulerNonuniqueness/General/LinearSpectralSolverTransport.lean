import EulerNonuniqueness.General.ComplexCubicResolution
import EulerNonuniqueness.General.FiniteSpectralHomological

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]

theorem complexCubicProjection_intertwines (transport : Space →ₗ[ℂ] Space)
    (source target : Space →L[ℂ] Space)
    (intertwines : ∀ vector, target (transport vector) = transport (source vector))
    (branch : Fin 3) (vector : Space) :
    complexCubicProjection target branch (transport vector) = transport (complexCubicProjection source branch vector) := by
  have twice : target (target (transport vector)) = transport (source (source vector)) := by
    rw [intertwines, intertwines]
  fin_cases branch
  · change transport vector + (4 : ℂ) • target (target (transport vector)) =
      transport (vector + (4 : ℂ) • source (source vector))
    rw [twice, map_add, map_smul]
  · change (-2 : ℂ) • target (target (transport vector)) - Complex.I • target (transport vector) =
      transport ((-2 : ℂ) • source (source vector) - Complex.I • source vector)
    rw [twice, intertwines, map_sub, map_smul, map_smul]
  · change (-2 : ℂ) • target (target (transport vector)) + Complex.I • target (transport vector) =
      transport ((-2 : ℂ) • source (source vector) + Complex.I • source vector)
    rw [twice, intertwines, map_add, map_smul, map_smul]

theorem complexCubicHomologicalSolver_intertwines (transport : Space →ₗ[ℂ] Space)
    (source target sourceNumerator targetNumerator : Space →L[ℂ] Space)
    (generatorIntertwines : ∀ vector, target (transport vector) = transport (source vector))
    (numeratorIntertwines : ∀ vector, targetNumerator (transport vector) = transport (sourceNumerator vector))
    (eigenvalue : Fin 3 → ℂ) (frequency : ℂ) (vector : Space) :
    finiteSpectralHomologicalSolver (complexCubicProjection target) eigenvalue frequency targetNumerator
        (transport vector) =
      transport (finiteSpectralHomologicalSolver (complexCubicProjection source) eigenvalue frequency sourceNumerator vector) := by
  simp only [finiteSpectralHomologicalSolver, spectralHomologicalBlock, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  rw [complexCubicProjection_intertwines transport source target generatorIntertwines,
    numeratorIntertwines, complexCubicProjection_intertwines transport source target generatorIntertwines]

end EulerNonuniqueness.General
