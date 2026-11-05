import EulerNonuniqueness.Section3.FiniteMovingPatchFamily
import EulerNonuniqueness.Section3.PatchStaticMoments
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem MovingMaterialPatch.boundary_periodic (path : MovingMaterialPatch) (time : ℝ) :
    Function.Periodic (path.boundary time) (2 * Real.pi) := by
  intro label
  dsimp only [MovingMaterialPatch.boundary]
  rw [PeriodicC1HolderHalf.periodic (path.shape time) label]

namespace FiniteMovingPatchFamily

variable {count : ℕ}

def patchMotion (family : FiniteMovingPatchFamily (count * 4)) : PatchMotion count where
  domain time index patch := (family.patch (finProdFinEquiv (index, patch))).domain time
  boundary time index patch := (family.patch (finProdFinEquiv (index, patch))).boundary time

theorem patchDensity_eq (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (time : ℝ) (index : Fin count) (patch : Fin 4) :
    Paper.patchDensity scales family.patchMotion time index patch = family.patchVorticity time (finProdFinEquiv (index, patch)) := by
  unfold Paper.patchDensity patchVorticity patchMotion
  rw [densityIdentity]

theorem patchVorticity_eq (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) :
    Paper.patchVorticity scales family.patchMotion = family.vorticity := by
  funext time position
  dsimp only [Paper.patchVorticity, quadrupoleDensity]
  simp_rw [family.patchDensity_eq scales densityIdentity]
  calc
    (∑ index : Fin count, ∑ patch : Fin 4, family.patchVorticity time (finProdFinEquiv (index, patch)) position) =
        ∑ pair : Fin count × Fin 4, family.patchVorticity time (finProdFinEquiv pair) position :=
      (Fintype.sum_prod_type (fun pair : Fin count × Fin 4 => family.patchVorticity time (finProdFinEquiv pair) position)).symm
    _ = family.vorticity time position := finProdFinEquiv.sum_comp (fun label => family.patchVorticity time label position)

theorem patchCentroid_eq (family : FiniteMovingPatchFamily (count * 4)) (time : ℝ) (index : Fin count) (patch : Fin 4) :
    Paper.patchCentroid family.patchMotion time index patch =
      (family.patch (finProdFinEquiv (index, patch))).centroid time := by
  rw [Paper.patchCentroid_eq_setAverage, MovingMaterialPatch.centroid_eq_setAverage]
  rfl

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
