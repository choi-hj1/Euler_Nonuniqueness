import EulerNonuniqueness.Section6.MovingForeignQuadrupole
import EulerNonuniqueness.Section6.MovingPatchFamilyQuadrupole
import EulerNonuniqueness.Section3.MovingCanonicalCentroidPointEquation
import EulerNonuniqueness.Section3.FiniteMovingPatchBiotSavart

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem externalPatch_biotSavart_eq_sum_quadrupoles {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (time : ℝ) (receiver : Fin count) (position : ℂ) :
    biotSavart (externalPatchVorticity scales family.patchMotion time receiver) position =
      ∑ source ∈ Finset.univ.erase receiver,
        biotSavart ((family.quadrupoleSubfamily source).vorticity time) position := by
  rw [family.externalPatchVorticity_eq_subfamily scales densityEquation time receiver,
    family.biotSavart_subfamily_eq_sum, foreignQuadrupolePatchLabels,
    Finset.sum_image (fun first _ second _ equality => finProdFinEquiv.injective equality)]
  simp only [Finset.product_eq_sprod]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro source _
  rw [(family.quadrupoleSubfamily source).biotSavart_eq_sum_patchVorticity]
  rfl

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
