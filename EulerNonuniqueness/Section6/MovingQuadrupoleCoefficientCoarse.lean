import EulerNonuniqueness.Section6.MovingQuadrupoleRelativeSeries

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

set_option maxHeartbeats 6000000

theorem quadrupolePointDifferenceEnvelope_coarse_bound
    (comparison : MovingPatchFamilySourceComparison 4) (circulation : ℝ) (firstCenter secondCenter : ℂ)
    {radius distance weight receiverScale sourceScale receiverState sourceState : ℝ}
    (circulationNonnegative : 0 ≤ circulation) (radiusNonnegative : 0 ≤ radius)
    (distancePositive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (receiverNonnegative : 0 ≤ receiverScale) (sourceNonnegative : 0 ≤ sourceScale)
    (receiverStateNonnegative : 0 ≤ receiverState) (sourceStateNonnegative : 0 ≤ sourceState)
    (radiusSmall : radius ≤ sourceScale)
    (ratioSmall : 8 * weight * comparison.receiverRadius / distance ≤ 1 / 2)
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
    comparison.quadrupolePointDifferenceEnvelope circulation firstCenter secondCenter radius distance weight ≤
      circulation * weight *
        (32 * sourceScale / distance ^ 3 + 512 * sourceScale ^ 2 / distance ^ 4 +
          4096 * sourceScale ^ 3 / distance ^ 5) * sourceState +
      circulation * weight *
        (256 * receiverScale * sourceScale / distance ^ 4 +
          4096 * receiverScale * sourceScale ^ 2 / distance ^ 5) * receiverState := by
  have coefficientBound : |circulation| / (2 * Real.pi) ≤ circulation := by
    rw [abs_of_nonneg circulationNonnegative]
    exact div_le_self circulationNonnegative (by linarith [Real.pi_gt_three])
  have ratioNonnegative : 0 ≤ weight * comparison.receiverRadius / distance := by
    exact div_nonneg (mul_nonneg weightNonnegative comparison.receiverRadius_nonnegative) distancePositive.le
  have firstDenominator : (1 / 2 : ℝ) ≤ 1 - 4 * weight * comparison.receiverRadius / distance := by
    have identity : 4 * weight * comparison.receiverRadius / distance = (8 * weight * comparison.receiverRadius / distance) / 2 := by ring
    rw [identity]
    nlinarith
  have secondDenominator : (1 / 2 : ℝ) ≤ 1 - 8 * weight * comparison.receiverRadius / distance := by linarith
  have firstInverse : (1 - 4 * weight * comparison.receiverRadius / distance)⁻¹ ≤ 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) firstDenominator
  have secondInverse : (1 - 8 * weight * comparison.receiverRadius / distance)⁻¹ ≤ 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) secondDenominator
  have estimate : comparison.quadrupolePointDifferenceEnvelope circulation firstCenter secondCenter radius distance weight ≤
      (weight * circulation * (4 * distance⁻¹ ^ 3 * (4 * sourceScale * sourceState) +
        32 * distance⁻¹ ^ 4 * sourceScale * (4 * sourceScale * sourceState))) * 2 +
      (weight * circulation * (32 * distance⁻¹ ^ 4 * (4 * sourceScale) +
        512 * distance⁻¹ ^ 5 * sourceScale * (4 * sourceScale)) *
          (receiverScale * receiverState + sourceScale * sourceState)) * 2 := by
    unfold quadrupolePointDifferenceEnvelope
    gcongr
  apply estimate.trans_eq
  field_simp
  <;> ring

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
