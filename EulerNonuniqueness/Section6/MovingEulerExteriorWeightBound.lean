import EulerNonuniqueness.Section6.FiniteExteriorWeightBound
import EulerNonuniqueness.Section6.PaperPatchCentroidAlgebra
import EulerNonuniqueness.Section3.FiniteMovingPatchMotion

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem patch_abs_mass_eq_circulation {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (scales : Scales) {horizon time : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (label : Fin (count * 4)) :
    |family.density label| * volume.real ((family.patch label).domain time) =
      scales.circulation ((finProdFinEquiv.symm label).1.val + 1) := by
  obtain ⟨⟨index, patch⟩, equality⟩ := finProdFinEquiv.surjective label
  subst label
  simp only [Equiv.symm_apply_apply, densityIdentity]
  exact evolution.patch_abs_density_mul_area inside amplitudePositive frequencyPositive ratioPositive index patch

theorem patchVorticity_integral_abs_eq_circulation {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (scales : Scales) {horizon time : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (label : Fin (count * 4)) :
    (∫ position, |family.patchVorticity time label position|) =
      scales.circulation ((finProdFinEquiv.symm label).1.val + 1) := by
  rw [family.patchVorticity_integral_abs]
  exact family.patch_abs_mass_eq_circulation scales evolution inside densityIdentity
    amplitudePositive frequencyPositive ratioPositive label

theorem integral_inverseSquare_subfamily_le_circulations {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (selected : Finset (Fin (count * 4))) (center : ℂ) (distance : Fin (count * 4) → ℝ)
    (positive : ∀ source ∈ selected, 0 < distance source)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance source ≤ ‖center - position‖) :
    (∫ position, inverseSquareVorticityWeight (family.subfamilyVorticity selected time) center position) ≤
      ∑ source ∈ selected, scales.circulation ((finProdFinEquiv.symm source).1.val + 1) / distance source ^ 2 := by
  have estimate := family.integral_inverseSquare_subfamily_le selected time center distance positive separated
  simpa only [family.patch_abs_mass_eq_circulation scales evolution inside densityIdentity
    amplitudePositive frequencyPositive ratioPositive] using estimate

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
