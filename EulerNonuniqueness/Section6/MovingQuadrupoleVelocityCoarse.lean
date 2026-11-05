import EulerNonuniqueness.Section6.MovingQuadrupoleVelocityRelative

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

set_option maxHeartbeats 4000000

theorem quadrupoleVelocityPointDifferenceEnvelope_coarse_bound
    (comparison : MovingPatchFamilySourceComparison 4) (circulation : ℝ) (firstCenter secondCenter : ℂ)
    {sourceRadius distance receiverScale sourceScale receiverState sourceState : ℝ}
    (circulationNonnegative : 0 ≤ circulation) (radiusNonnegative : 0 ≤ sourceRadius)
    (distancePositive : 0 < distance) (receiverPositive : 0 < receiverScale)
    (sourceNonnegative : 0 ≤ sourceScale) (radiusSmall : sourceRadius ≤ sourceScale)
    (momentDifference : ‖Section6.fourPointSignedMoment (fun patch =>
        (comparison.first.patch patch).center comparison.time - firstCenter) -
      Section6.fourPointSignedMoment (fun patch =>
        (comparison.second.patch patch).center comparison.time - secondCenter)‖ ≤ 4 * sourceScale * sourceState)
    (shapeDifference : (∑ patch : Fin 4,
      ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
        ((comparison.second.patch patch).center comparison.time - secondCenter)‖) ≤ 4 * sourceScale * sourceState)
    (referenceMoment : ‖Section6.fourPointSignedMoment (fun patch =>
      (comparison.second.patch patch).center comparison.time - secondCenter)‖ ≤ 4 * sourceScale)
    (referencePositions : (∑ patch : Fin 4,
      ‖(comparison.second.patch patch).center comparison.time - secondCenter‖) ≤ 4 * sourceScale)
    (receiverDifference : ‖(comparison.firstReceiver comparison.time - firstCenter) -
      (comparison.secondReceiver comparison.time - secondCenter)‖ ≤
        receiverScale * receiverState + sourceScale * sourceState) :
    comparison.quadrupoleVelocityPointDifferenceEnvelope circulation firstCenter secondCenter sourceRadius distance /
        receiverScale ≤
      circulation *
        (4 * sourceScale / (receiverScale * distance ^ 2) +
          16 * sourceScale ^ 2 / (receiverScale * distance ^ 3) +
          24 * sourceScale ^ 3 / (receiverScale * distance ^ 4)) * sourceState +
      circulation * (8 * sourceScale / distance ^ 3 + 24 * sourceScale ^ 2 / distance ^ 4) * receiverState := by
  have coefficientBound : |circulation / (2 * Real.pi)| ≤ circulation := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_self circulationNonnegative (by linarith [Real.pi_gt_three])
  have estimate : comparison.quadrupoleVelocityPointDifferenceEnvelope circulation firstCenter secondCenter sourceRadius distance ≤
      circulation * (distance⁻¹ ^ 2 * (4 * sourceScale * sourceState) +
        2 * distance⁻¹ ^ 3 * sourceScale * (4 * sourceScale * sourceState)) +
      circulation * (2 * distance⁻¹ ^ 3 * (4 * sourceScale) +
        6 * distance⁻¹ ^ 4 * sourceScale * (4 * sourceScale)) *
          (receiverScale * receiverState + sourceScale * sourceState) := by
    unfold quadrupoleVelocityPointDifferenceEnvelope
    gcongr
  apply (div_le_div_of_nonneg_right estimate receiverPositive.le).trans_eq
  field_simp
  <;> ring

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
