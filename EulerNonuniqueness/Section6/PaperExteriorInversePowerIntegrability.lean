import EulerNonuniqueness.Section6.PaperMovingInversePowerMoment
import EulerNonuniqueness.Section6.MovingExternalPatchField

noncomputable section

open Set MeasureTheory Filter

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.integrable_patch_inverse_power_multiplier
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (patch : Fin 4) (center : ℂ) {distance : ℝ}
    (positive : 0 < distance)
    (separated : ∀ position ∈ motion.domain time index patch, distance ≤ ‖center - position‖)
    (power : ℕ) {field : ℂ → ℂ} (fieldContinuous : Continuous field) :
    Integrable (fun position => patchDensity scales motion time index patch position •
      (field position * (star (center - position))⁻¹ ^ power)) := by
  have continuous : Continuous (fun position => field position *
      Section6.smoothConjugateInversePower distance power (center - position)) :=
    fieldContinuous.mul ((Section6.smoothConjugateInversePower_contDiff positive power).continuous.comp
      (continuous_const.sub continuous_id))
  have modified := evolution.integrable_patchDensity_smul_continuous inside index patch continuous
  apply modified.congr
  apply Eventually.of_forall
  intro position
  by_cases member : position ∈ motion.domain time index patch
  · have kernel := (Section6.smoothConjugateInversePower_eventuallyEq positive power
      (separated position member)).self_of_nhds
    change patchDensity scales motion time index patch position • _ =
      patchDensity scales motion time index patch position • _
    rw [kernel]
  · simp only [patchDensity, indicator_of_not_mem member, zero_smul]

theorem FinitePatchEvolution.integral_externalPatch_inverse_power_eq_sum
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (center : ℂ) {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch position,
      position ∈ motion.domain time source patch → distance ≤ ‖center - position‖)
    (power : ℕ) {field : ℂ → ℂ} (fieldContinuous : Continuous field) :
    (∫ position, externalPatchVorticity scales motion time index position •
      (field position * (star (center - position))⁻¹ ^ power)) =
      ∑ source ∈ Finset.univ.erase index, ∑ patch : Fin 4,
        ∫ position, patchDensity scales motion time source patch position •
          (field position * (star (center - position))⁻¹ ^ power) := by
  classical
  have individual (source : Fin count) (member : source ∈ Finset.univ.erase index) (patch : Fin 4) :=
    evolution.integrable_patch_inverse_power_multiplier inside source patch center positive
      (separated source member patch) power fieldContinuous
  simp only [externalPatchVorticity, quadrupoleDensity, Finset.sum_smul]
  rw [integral_finset_sum _ (fun source member => integrable_finset_sum _
    (fun patch _ => individual source member patch))]
  apply Finset.sum_congr rfl
  intro source member
  exact integral_finset_sum _ (fun patch _ => individual source member patch)

end EulerNonuniqueness.Paper
