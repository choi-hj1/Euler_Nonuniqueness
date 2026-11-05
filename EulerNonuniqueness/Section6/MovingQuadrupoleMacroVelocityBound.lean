import EulerNonuniqueness.Section6.MovingQuadrupoleMacroCoefficientBound
import EulerNonuniqueness.Section6.MovingPatchVelocityCoarse

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem quadrupole_velocity_macro_state_bound
    (comparison : MovingPatchFamilySourceComparison 4) (firstCenter secondCenter : ℂ)
    {circulation constant radius distance receiverScale sourceScale receiverState : ℝ}
    (circulationNonnegative : 0 ≤ circulation) (constantNonnegative : 0 ≤ constant)
    (radiusNonnegative : 0 ≤ radius) (radiusSmall : radius ≤ sourceScale)
    (distancePositive : 0 < distance)
    (receiverPositive : 0 < receiverScale) (sourcePositive : 0 < sourceScale)
    (receiverStateNonnegative : 0 ≤ receiverState)
    (referencePositions : ∀ patch, ‖(comparison.second.patch patch).center comparison.time - secondCenter‖ ≤ sourceScale)
    (receiverDifference : ‖comparison.firstReceiver comparison.time - comparison.secondReceiver comparison.time‖ ≤ receiverScale * receiverState)
    (massBound : ∀ patch, |(comparison.source patch).density| * (comparison.source patch).first.radius ^ 2 ≤ circulation)
    (radiusBound : ∀ patch, (comparison.source patch).first.radius ≤ sourceScale)
    (separated : ∀ patch, distance ≤ ‖(comparison.source patch).secondReceiver - (comparison.source patch).second.center comparison.time‖) :
    let state := comparison.relativeMacroState firstCenter secondCenter sourceScale
    (comparison.quadrupoleVelocityPointDifferenceEnvelope circulation firstCenter secondCenter radius distance +
      (∑ patch : Fin 4, ((comparison.source patch).velocityCentroidCorrectionCenterEnvelope distance +
        (comparison.source patch).velocityCentroidCorrectionShapeEnvelope constant))) / receiverScale ≤
      circulation * (4 * sourceScale / (receiverScale * distance ^ 2) +
        (16 + 384 * constant) * sourceScale ^ 2 / (receiverScale * distance ^ 3) +
        72 * sourceScale ^ 3 / (receiverScale * distance ^ 4)) * state +
      circulation * (8 * sourceScale / distance ^ 3 + 72 * sourceScale ^ 2 / distance ^ 4) * receiverState := by
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
  have pointBound := comparison.quadrupoleVelocityPointDifferenceEnvelope_coarse_bound circulation firstCenter secondCenter
    circulationNonnegative radiusNonnegative distancePositive receiverPositive sourcePositive.le radiusSmall
    (momentDifference.trans (by dsimp only [state]; nlinarith))
    (shapeDifference.trans (by dsimp only [state]; nlinarith)) referenceMoment referenceSum centeredReceiver
  have patchBound (patch : Fin 4) := (comparison.source patch).velocityCentroidCorrectionEnvelopes_coarse_bound
    circulationNonnegative constantNonnegative distancePositive receiverPositive (massBound patch) (radiusBound patch) (separated patch)
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
  dsimp only
  rw [add_div, Finset.sum_div]
  apply (add_le_add pointBound summed).trans_eq
  ring

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

