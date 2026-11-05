import EulerNonuniqueness.Section6.PaperQuadrupoleStrainDerivative
import EulerNonuniqueness.Section6.PaperExternalTaylor

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.externalPatch_complexStrain_sum
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (distance : Fin count → ℝ) {center : ℂ}
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
      distance source ≤ ‖center - location‖) :
    Section6.vorticityComplexStrain (externalPatchVorticity scales motion time index) center =
      ∑ source ∈ Finset.univ.erase index,
        Section6.vorticityComplexStrain (quadrupoleDensity scales motion time source) center := by
  have integrable (source : Fin count) (member : source ∈ Finset.univ.erase index) :
      Integrable (fun location => quadrupoleDensity scales motion time source location •
        Section6.biotSavartKernelStrain center location) := by
    simp only [quadrupoleDensity, Finset.sum_smul]
    exact integrable_finset_sum _ fun patch _ => evolution.integrable_patchDensity_kernelStrain inside source patch
      (positive source member) (separated source member patch)
  simp only [Section6.vorticityComplexStrain, externalPatchVorticity, Finset.sum_smul]
  exact integral_finset_sum _ integrable

theorem FinitePatchEvolution.externalPatch_biotSavart_hasFDerivAt_complexStrain
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (distance : Fin count → ℝ) {center : ℂ}
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
      distance source ≤ ‖center - location‖) :
    HasFDerivAt (biotSavart (externalPatchVorticity scales motion time index))
      (Section6.vorticityComplexStrain (externalPatchVorticity scales motion time index) center •
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)) center := by
  have identity : biotSavart (externalPatchVorticity scales motion time index) =
      fun position => ∑ source ∈ Finset.univ.erase index, biotSavart (quadrupoleDensity scales motion time source) position := by
    funext position
    rw [evolution.externalPatch_biotSavart_eq_sum inside index position]
    exact Finset.sum_congr rfl fun source _ => (evolution.quadrupole_biotSavart_eq_sum_patch inside source position).symm
  have operatorIdentity :
      (∑ source ∈ Finset.univ.erase index,
        Section6.vorticityComplexStrain (quadrupoleDensity scales motion time source) center) •
          (Complex.conjCLE : ℂ →L[ℝ] ℂ) =
      ∑ source ∈ Finset.univ.erase index,
        Section6.vorticityComplexStrain (quadrupoleDensity scales motion time source) center •
          (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
    ext increment
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, smul_eq_mul, Finset.sum_mul]
  rw [identity, evolution.externalPatch_complexStrain_sum inside index distance positive separated, operatorIdentity]
  exact HasFDerivAt.sum fun source member => evolution.quadrupole_biotSavart_hasFDerivAt_complexStrain inside source
    (positive source member) (separated source member)

end EulerNonuniqueness.Paper
