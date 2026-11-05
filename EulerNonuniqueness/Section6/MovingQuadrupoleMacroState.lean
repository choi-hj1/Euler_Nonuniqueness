import EulerNonuniqueness.Section6.MovingQuadrupoleVelocityCoarse
import EulerNonuniqueness.Section6.FourPointInversePowerRelative
import EulerNonuniqueness.Section6.FourPointMomentControl

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

def relativeMacroState (comparison : MovingPatchFamilySourceComparison 4)
    (firstCenter secondCenter : ℂ) (scale : ℝ) : ℝ :=
  (‖firstCenter - secondCenter‖ + ∑ patch : Fin 4,
    ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
      ((comparison.second.patch patch).center comparison.time - secondCenter)‖) / scale +
    ∑ patch : Fin 4, (comparison.source patch).spectralDifferenceBudget

theorem relativeMacroState_nonnegative (comparison : MovingPatchFamilySourceComparison 4)
    (firstCenter secondCenter : ℂ) {scale : ℝ} (scaleNonnegative : 0 ≤ scale) :
    0 ≤ comparison.relativeMacroState firstCenter secondCenter scale := by
  unfold relativeMacroState
  exact add_nonneg (div_nonneg (add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)) scaleNonnegative)
    (Finset.sum_nonneg fun patch _ => (comparison.source patch).spectralDifferenceBudget_nonnegative)

theorem relativeMacroState_position_budget (comparison : MovingPatchFamilySourceComparison 4)
    (firstCenter secondCenter : ℂ) {scale : ℝ} (scalePositive : 0 < scale) :
    ‖firstCenter - secondCenter‖ + (∑ patch : Fin 4,
      ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
        ((comparison.second.patch patch).center comparison.time - secondCenter)‖) ≤
      scale * comparison.relativeMacroState firstCenter secondCenter scale := by
  unfold relativeMacroState
  rw [mul_add, mul_div_cancel₀ _ scalePositive.ne']
  exact le_add_of_nonneg_right (mul_nonneg scalePositive.le
    (Finset.sum_nonneg fun patch _ => (comparison.source patch).spectralDifferenceBudget_nonnegative))

theorem relativeMacroState_shape_budget (comparison : MovingPatchFamilySourceComparison 4)
    (firstCenter secondCenter : ℂ) {scale : ℝ} (scalePositive : 0 < scale) :
    (∑ patch : Fin 4,
      ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
        ((comparison.second.patch patch).center comparison.time - secondCenter)‖) ≤
      scale * comparison.relativeMacroState firstCenter secondCenter scale :=
  (le_add_of_nonneg_left (norm_nonneg _)).trans
    (comparison.relativeMacroState_position_budget firstCenter secondCenter scalePositive)

theorem relativeMacroState_spectral_budget (comparison : MovingPatchFamilySourceComparison 4)
    (firstCenter secondCenter : ℂ) {scale : ℝ} (scalePositive : 0 < scale) (patch : Fin 4) :
    (comparison.source patch).spectralDifferenceBudget ≤ comparison.relativeMacroState firstCenter secondCenter scale := by
  have individual := Finset.single_le_sum
    (fun label (_ : label ∈ (Finset.univ : Finset (Fin 4))) => (comparison.source label).spectralDifferenceBudget_nonnegative)
    (Finset.mem_univ patch)
  exact individual.trans (le_add_of_nonneg_left (div_nonneg
    (add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)) scalePositive.le))

theorem relativeMacroState_patch_difference (comparison : MovingPatchFamilySourceComparison 4)
    (firstCenter secondCenter : ℂ) {scale : ℝ} (scalePositive : 0 < scale) (patch : Fin 4) :
    ‖(comparison.first.patch patch).center comparison.time - (comparison.second.patch patch).center comparison.time‖ ≤
      scale * comparison.relativeMacroState firstCenter secondCenter scale := by
  have individual := Finset.single_le_sum (fun label (_ : label ∈ (Finset.univ : Finset (Fin 4))) =>
    norm_nonneg (((comparison.first.patch label).center comparison.time - firstCenter) -
      ((comparison.second.patch label).center comparison.time - secondCenter))) (Finset.mem_univ patch)
  have identity : (comparison.first.patch patch).center comparison.time - (comparison.second.patch patch).center comparison.time =
      (firstCenter - secondCenter) + (((comparison.first.patch patch).center comparison.time - firstCenter) -
        ((comparison.second.patch patch).center comparison.time - secondCenter)) := by abel
  rw [identity]
  exact (norm_add_le _ _).trans ((add_le_add_left individual _).trans
    (comparison.relativeMacroState_position_budget firstCenter secondCenter scalePositive))

theorem relativeMacroState_moment_difference (comparison : MovingPatchFamilySourceComparison 4)
    (firstCenter secondCenter : ℂ) {scale : ℝ} (scalePositive : 0 < scale) :
    ‖Section6.fourPointSignedMoment (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter) -
      Section6.fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)‖ ≤
      scale * comparison.relativeMacroState firstCenter secondCenter scale := by
  rw [← Section6.fourPointSignedMoment_sub]
  apply le_trans (norm_sum_le _ _)
  have identity : (∑ patch : Fin 4,
      ‖(Section6.fourPointSign patch : ℂ) *
        (((comparison.first.patch patch).center comparison.time - firstCenter) -
          ((comparison.second.patch patch).center comparison.time - secondCenter))‖) =
      ∑ patch : Fin 4, ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
        ((comparison.second.patch patch).center comparison.time - secondCenter)‖ := by
    apply Finset.sum_congr rfl
    intro patch _
    have signNorm : ‖(Section6.fourPointSign patch : ℂ)‖ = 1 := by
      by_cases positive : patch.val < 2 <;> simp [Section6.fourPointSign, positive]
    rw [norm_mul, signNorm, one_mul]
  rw [identity]
  exact comparison.relativeMacroState_shape_budget firstCenter secondCenter scalePositive

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
