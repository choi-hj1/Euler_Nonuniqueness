import EulerNonuniqueness.Section3.MovingCanonicalCentroidPointEquation
import EulerNonuniqueness.Section6.MovingPatchFamilyQuadrupole
import EulerNonuniqueness.Section3.FiniteMovingPatchBiotSavart

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem biotSavart_erased_eq_own_and_foreign_quadrupoles {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (receiver : Fin count × Fin 4)
    (time : ℝ) (position : ℂ) :
    biotSavart (family.subfamilyVorticity (Finset.univ.erase (finProdFinEquiv receiver)) time) position =
      biotSavart ((family.quadrupoleSubfamily receiver.1).subfamilyVorticity
        (Finset.univ.erase receiver.2) time) position +
      ∑ source ∈ Finset.univ.erase receiver.1,
        biotSavart ((family.quadrupoleSubfamily source).vorticity time) position := by
  rw [family.biotSavart_subfamily_eq_sum,
    (family.quadrupoleSubfamily receiver.1).biotSavart_subfamily_eq_sum]
  simp_rw [biotSavart_eq_sum_patchVorticity]
  exact EulerNonuniqueness.General.sum_erase_equiv_prod finProdFinEquiv
    (fun label => biotSavart (family.patchVorticity time label) position) receiver.1 receiver.2

theorem biotSavart_erased_eq_internal_centroids_and_foreign {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (receiver : Fin count × Fin 4)
    (time : ℝ) (position : ℂ) :
    biotSavart (family.subfamilyVorticity (Finset.univ.erase (finProdFinEquiv receiver)) time) position =
      (∑ patch ∈ Finset.univ.erase receiver.2,
        ((family.quadrupoleSubfamily receiver.1).density patch *
          volume.real (((family.quadrupoleSubfamily receiver.1).patch patch).domain time)) •
          biotSavartKernel (position - ((family.quadrupoleSubfamily receiver.1).patch patch).center time)) +
      (∑ patch ∈ Finset.univ.erase receiver.2,
        ((family.quadrupoleSubfamily receiver.1).patch patch).sourceVelocityCentroidCorrection
          ((family.quadrupoleSubfamily receiver.1).density patch) position time) +
      ∑ source ∈ Finset.univ.erase receiver.1,
        biotSavart ((family.quadrupoleSubfamily source).vorticity time) position := by
  rw [family.biotSavart_erased_eq_own_and_foreign_quadrupoles,
    (family.quadrupoleSubfamily receiver.1).biotSavart_subfamily_eq_centroid_and_corrections]

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
