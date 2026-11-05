import EulerNonuniqueness.Section3.FiniteMovingPatchFamily
import EulerNonuniqueness.Section6.PatchCrossInteraction

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem biotSavart_eq_sum_patchVorticity {count : ℕ} (family : FiniteMovingPatchFamily count)
    (time : ℝ) (position : ℂ) :
    biotSavart (family.vorticity time) position =
      ∑ index, biotSavart (family.patchVorticity time index) position := by
  have integrable (index : Fin count) : Integrable (fun source => family.patchVorticity time index source •
      biotSavartKernel (position - source)) :=
    integrable_biotSavart_integrand_of_L1_L4 (family.patchVorticity_integrable time index)
      (family.patchVorticity_memLp time index _) position
  unfold biotSavart vorticity
  simp_rw [Finset.sum_smul]
  exact integral_finset_sum Finset.univ (fun index _ => integrable index)

theorem biotSavart_eq_sum_domain_integrals {count : ℕ} (family : FiniteMovingPatchFamily count)
    (time : ℝ) (position : ℂ) :
    biotSavart (family.vorticity time) position =
      ∑ index, family.density index • (∫ source in (family.patch index).domain time, biotSavartKernel (position - source)) := by
  rw [family.biotSavart_eq_sum_patchVorticity]
  apply Finset.sum_congr rfl
  intro index member
  exact Section6.biotSavart_indicator_density_integral ((family.patch index).domain_isOpen time).measurableSet _ _

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
