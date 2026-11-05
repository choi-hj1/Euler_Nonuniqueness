import EulerNonuniqueness.Section6.PaperQuadrupoleStaticMoments
import EulerNonuniqueness.Section3.FinitePatchBounds

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

theorem patchVorticity_eq_external_add_quadrupole {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) :
    patchVorticity scales motion time = externalPatchVorticity scales motion time index +
      quadrupoleDensity scales motion time index := by
  classical
  funext position
  exact (Finset.sum_erase_add (s := Finset.univ)
    (f := fun source : Fin count => quadrupoleDensity scales motion time source position)
    (Finset.mem_univ index)).symm

theorem FinitePatchEvolution.externalPatchVorticity_integrable
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) : Integrable (externalPatchVorticity scales motion time index) := by
  classical
  apply integrable_finset_sum
  intro source _
  exact evolution.quadrupoleDensity_integrable inside source

theorem FinitePatchEvolution.externalPatchVorticity_memLp
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (exponent : ℝ≥0∞) :
    MemLp (externalPatchVorticity scales motion time index) exponent volume := by
  classical
  have identity : externalPatchVorticity scales motion time index =
      ∑ source ∈ Finset.univ.erase index, quadrupoleDensity scales motion time source := by
    funext position
    simp only [externalPatchVorticity, Finset.sum_apply]
  rw [identity]
  apply memLp_finset_sum'
  intro source _
  exact quadrupoleDensity_memLp scales motion time source
    (fun patch => (evolution.2.2.2.1 time inside source patch).1)
    (fun patch => (evolution.2.2.2.1 time inside source patch).2.1) exponent

theorem FinitePatchEvolution.externalPatchVorticity_compactSupport
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) : HasCompactSupport (externalPatchVorticity scales motion time index) := by
  classical
  have identity : externalPatchVorticity scales motion time index =
      ∑ source ∈ Finset.univ.erase index, quadrupoleDensity scales motion time source := by
    funext position
    simp only [externalPatchVorticity, Finset.sum_apply]
  rw [identity]
  exact HasCompactSupport.finset_sum _ (fun source _ =>
    quadrupoleDensity_hasCompactSupport scales motion time source
      (fun patch => (evolution.2.2.2.1 time inside source patch).2.1))

theorem externalPatchVorticity_abs_le {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (position : ℂ) :
    |externalPatchVorticity scales motion time index position| ≤
      ∑ source ∈ Finset.univ.erase index, ∑ patch : Fin 4,
        |patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4| := by
  classical
  change ‖∑ source ∈ Finset.univ.erase index, quadrupoleDensity scales motion time source position‖ ≤ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro source _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro patch _
  by_cases member : position ∈ motion.domain time source patch
  · simp only [patchDensity, indicator_of_mem member, Real.norm_eq_abs, le_refl]
  · simp only [patchDensity, indicator_of_not_mem member, norm_zero]
    exact abs_nonneg _

theorem externalPatchVorticity_support_separated {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (center : ℂ) (distance : ℝ)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch position,
      position ∈ motion.domain time source patch → distance ≤ ‖center - position‖) :
    ∀ position ∈ Function.support (externalPatchVorticity scales motion time index), distance ≤ ‖center - position‖ := by
  classical
  intro position nonzero
  by_contra outside
  have vanishes (source : Fin count) (member : source ∈ Finset.univ.erase index) (patch : Fin 4) :
      patchDensity scales motion time source patch position = 0 := by
    apply indicator_of_not_mem
    exact fun inDomain => outside (separated source member patch position inDomain)
  apply nonzero
  apply Finset.sum_eq_zero
  intro source member
  apply Finset.sum_eq_zero
  intro patch _
  exact vanishes source member patch

end EulerNonuniqueness.Paper
