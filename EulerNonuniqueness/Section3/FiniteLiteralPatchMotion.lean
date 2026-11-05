import EulerNonuniqueness.Section3.FiniteLiteralPatchFlow
import EulerNonuniqueness.Section4.ReferenceStatement
import Mathlib.Logic.Equiv.Fin.Basic

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}

def patchMotion (flow : FiniteLiteralPatchFlow configuration) : PatchMotion count where
  domain time index patch := flow.domain time (finProdFinEquiv (index, patch))
  boundary time index patch := flow.boundary time (finProdFinEquiv (index, patch))

theorem patchDensity_eq (flow : FiniteLiteralPatchFlow configuration) (scales : Scales)
    (density_eq : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (time : ℝ) (index : Fin count) (patch : Fin 4) :
    patchDensity scales flow.patchMotion time index patch = fun position =>
      configuration.density (finProdFinEquiv (index, patch)) *
        (flow.domain time (finProdFinEquiv (index, patch))).indicator (fun _ => (1 : ℝ)) position := by
  funext position
  rw [density_eq]
  by_cases member : position ∈ flow.domain time (finProdFinEquiv (index, patch)) <;>
    simp [patchDensity, patchMotion, member]

theorem patchVorticity_eq (flow : FiniteLiteralPatchFlow configuration) (scales : Scales)
    (density_eq : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) :
    patchVorticity scales flow.patchMotion = flow.vorticity := by
  funext time position
  dsimp only [patchVorticity, quadrupoleDensity]
  simp_rw [flow.patchDensity_eq scales density_eq]
  change (∑ index : Fin count, ∑ patch : Fin 4,
    configuration.density (finProdFinEquiv (index, patch)) *
      (flow.domain time (finProdFinEquiv (index, patch))).indicator (fun _ => (1 : ℝ)) position) = _
  calc
    _ = ∑ pair : Fin count × Fin 4, configuration.density (finProdFinEquiv pair) *
        (flow.domain time (finProdFinEquiv pair)).indicator (fun _ => (1 : ℝ)) position :=
      (Fintype.sum_prod_type (fun pair : Fin count × Fin 4 => configuration.density (finProdFinEquiv pair) *
        (flow.domain time (finProdFinEquiv pair)).indicator (fun _ => (1 : ℝ)) position)).symm
    _ = _ := finProdFinEquiv.sum_comp (fun label => configuration.density label *
      (flow.domain time label).indicator (fun _ => (1 : ℝ)) position)

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
