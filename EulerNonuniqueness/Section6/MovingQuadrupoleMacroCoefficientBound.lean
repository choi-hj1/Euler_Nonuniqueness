import EulerNonuniqueness.Section6.MovingQuadrupoleMacroState
import EulerNonuniqueness.Section6.MovingQuadrupoleCoefficientCoarse
import EulerNonuniqueness.Section6.MovingPatchCoefficientCoarse

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem relativeMacroState_center_difference (comparison : MovingPatchFamilySourceComparison 4)
    (firstCenter secondCenter : ℂ) {scale : ℝ} (scalePositive : 0 < scale) :
    ‖firstCenter - secondCenter‖ ≤ scale * comparison.relativeMacroState firstCenter secondCenter scale :=
  (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)).trans
    (comparison.relativeMacroState_position_budget firstCenter secondCenter scalePositive)

theorem quadrupole_coefficient_macro_state_bound
    (comparison : MovingPatchFamilySourceComparison 4) (firstCenter secondCenter : ℂ)
    {circulation constant radius distance weight receiverScale sourceScale receiverState : ℝ}
    (circulationNonnegative : 0 ≤ circulation) (constantNonnegative : 0 ≤ constant)
    (radiusNonnegative : 0 ≤ radius) (radiusSmall : radius ≤ sourceScale)
    (distancePositive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (receiverNonnegative : 0 ≤ receiverScale) (sourcePositive : 0 < sourceScale)
    (receiverStateNonnegative : 0 ≤ receiverState)
    (ratioSmall : 8 * weight * comparison.receiverRadius / distance ≤ 1 / 2)
    (referencePositions : ∀ patch, ‖(comparison.second.patch patch).center comparison.time - secondCenter‖ ≤ sourceScale)
    (receiverDifference : ‖comparison.firstReceiver comparison.time - comparison.secondReceiver comparison.time‖ ≤ receiverScale * receiverState)
    (massBound : ∀ patch, |(comparison.source patch).density| * (comparison.source patch).first.radius ^ 2 ≤ circulation)
    (radiusBound : ∀ patch, (comparison.source patch).first.radius ≤ sourceScale)
    (separated : ∀ patch, distance ≤ ‖(comparison.source patch).secondReceiver - (comparison.source patch).second.center comparison.time‖) :
    let state := comparison.relativeMacroState firstCenter secondCenter sourceScale
    comparison.quadrupolePointDifferenceEnvelope circulation firstCenter secondCenter radius distance weight +
      2 * (∑ patch : Fin 4, ((comparison.source patch).centroidCorrectionCenterEnvelope distance weight +
        (comparison.source patch).centeredShapeDifferenceEnvelope constant weight)) ≤
      circulation * weight * (32 * sourceScale / distance ^ 3 +
        (512 + 73728 * constant) * sourceScale ^ 2 / distance ^ 4 +
        12288 * sourceScale ^ 3 / distance ^ 5) * state +
      circulation * weight * (256 * receiverScale * sourceScale / distance ^ 4 +
        12288 * receiverScale * sourceScale ^ 2 / distance ^ 5) * receiverState := by
  let state := comparison.relativeMacroState firstCenter secondCenter sourceScale
  have stateNonnegative : 0 ≤ state := comparison.relativeMacroState_nonnegative firstCenter secondCenter sourcePositive.le
  have momentDifference := comparison.relativeMacroState_moment_difference firstCenter secondCenter sourcePositive
  have shapeDifference := comparison.relativeMacroState_shape_budget firstCenter secondCenter sourcePositive
  have sourceCenter := comparison.relativeMacroState_center_difference firstCenter secondCenter sourcePositive
  have referenceSum : (∑ patch : Fin 4, ‖(comparison.second.patch patch).center comparison.time - secondCenter‖) ≤ 4 * sourceScale := by
    have actual := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => referencePositions patch)
    simpa using actual
  have referenceMoment : ‖Section6.fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)‖ ≤ 4 * sourceScale := by
    apply (Section6.fourPointSignedMoment_norm_le _).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
    exact (pi_norm_le_iff_of_nonneg sourcePositive.le).mpr referencePositions
  have centeredReceiver : ‖(comparison.firstReceiver comparison.time - firstCenter) -
      (comparison.secondReceiver comparison.time - secondCenter)‖ ≤ receiverScale * receiverState + sourceScale * state := by
    have identity : (comparison.firstReceiver comparison.time - firstCenter) -
        (comparison.secondReceiver comparison.time - secondCenter) =
        (comparison.firstReceiver comparison.time - comparison.secondReceiver comparison.time) - (firstCenter - secondCenter) := by abel
    rw [identity]
    exact (norm_sub_le _ _).trans (add_le_add receiverDifference sourceCenter)
  have pointBound := comparison.quadrupolePointDifferenceEnvelope_coarse_bound circulation firstCenter secondCenter
    circulationNonnegative radiusNonnegative distancePositive weightNonnegative receiverNonnegative sourcePositive.le
    receiverStateNonnegative stateNonnegative radiusSmall ratioSmall
    (momentDifference.trans (by dsimp only [state]; nlinarith))
    (shapeDifference.trans (by dsimp only [state]; nlinarith)) referenceMoment referenceSum centeredReceiver
  have patchBound (patch : Fin 4) := (comparison.source patch).centroidCorrectionEnvelopes_coarse_bound
    circulationNonnegative constantNonnegative distancePositive weightNonnegative receiverNonnegative sourcePositive.le
    receiverStateNonnegative stateNonnegative (massBound patch) (radiusBound patch) (separated patch)
    (by
      have sourceDifference := comparison.relativeMacroState_patch_difference firstCenter secondCenter sourcePositive patch
      have identity : (comparison.source patch).displacementDifference =
          (comparison.firstReceiver comparison.time - comparison.secondReceiver comparison.time) -
            ((comparison.first.patch patch).center comparison.time - (comparison.second.patch patch).center comparison.time) := by
        unfold MovingPatchSourceComparison.displacementDifference source
        abel
      rw [identity]
      exact (norm_sub_le _ _).trans (add_le_add receiverDifference sourceDifference))
    (comparison.relativeMacroState_spectral_budget firstCenter secondCenter sourcePositive patch)
  have summed := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => patchBound patch)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at summed
  apply (add_le_add pointBound (mul_le_mul_of_nonneg_left summed (by norm_num : (0 : ℝ) ≤ 2))).trans_eq
  dsimp only
  ring

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
