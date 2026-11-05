import EulerNonuniqueness.Section6.PaperExternalStrainDerivative
import EulerNonuniqueness.Section6.PhysicalVorticityStrainMultipole

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

theorem externalQuadrupoleStrain_eq_complexStrain {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (center : ℝ → ℂ) (index : Fin count) (time : ℝ) :
    externalQuadrupoleStrain scales motion center index time =
      Section6.vorticityComplexStrain (externalPatchVorticity scales motion time index) (center time) := by
  rw [Section6.vorticityComplexStrain_cauchy_identity]
  unfold externalQuadrupoleStrain
  have conjugateIntegral := integral_conj (μ := volume)
    (f := fun position : ℂ => externalPatchVorticity scales motion time index position •
      (1 / (center time - position) ^ 2 : ℂ))
  change (∫ position : ℂ, star (externalPatchVorticity scales motion time index position •
      (1 / (center time - position) ^ 2 : ℂ))) =
    star (∫ position : ℂ, externalPatchVorticity scales motion time index position •
      (1 / (center time - position) ^ 2 : ℂ)) at conjugateIntegral
  rw [← conjugateIntegral]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, neg_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with position
  simp [one_div, Complex.star_def]

end EulerNonuniqueness.Paper
