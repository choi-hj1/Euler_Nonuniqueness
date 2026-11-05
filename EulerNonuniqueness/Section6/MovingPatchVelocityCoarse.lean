import EulerNonuniqueness.Section6.MovingPatchVelocityCorrectionRelative

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchSourceComparison

set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem velocityCentroidCorrectionEnvelopes_coarse_bound
    (comparison : MovingPatchSourceComparison)
    {circulation constant distance receiverScale sourceScale receiverState sourceState : ℝ}
    (circulationNonnegative : 0 ≤ circulation) (constantNonnegative : 0 ≤ constant)
    (distancePositive : 0 < distance) (receiverPositive : 0 < receiverScale)
    (massBound : |comparison.density| * comparison.first.radius ^ 2 ≤ circulation)
    (radiusBound : comparison.first.radius ≤ sourceScale)
    (separated : distance ≤ ‖comparison.secondReceiver - comparison.second.center comparison.time‖)
    (displacementBound : ‖comparison.displacementDifference‖ ≤
      receiverScale * receiverState + sourceScale * sourceState)
    (shapeBound : comparison.spectralDifferenceBudget ≤ sourceState) :
    (comparison.velocityCentroidCorrectionCenterEnvelope distance +
      comparison.velocityCentroidCorrectionShapeEnvelope constant) / receiverScale ≤
      circulation *
        (12 * sourceScale ^ 3 / (receiverScale * distance ^ 4) +
          96 * constant * sourceScale ^ 2 / (receiverScale * distance ^ 3)) * sourceState +
      12 * circulation * sourceScale ^ 2 / distance ^ 4 * receiverState := by
  let actualDistance := ‖comparison.secondReceiver - comparison.second.center comparison.time‖
  have actualPositive : 0 < actualDistance := distancePositive.trans_le separated
  have radiusNonnegative := comparison.first.radius_positive.le
  have fourthMoment : |comparison.density| * comparison.first.radius ^ 4 ≤
      circulation * sourceScale ^ 2 := by
    calc
      _ = (|comparison.density| * comparison.first.radius ^ 2) * comparison.first.radius ^ 2 := by ring
      _ ≤ circulation * comparison.first.radius ^ 2 :=
        mul_le_mul_of_nonneg_right massBound (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ radiusNonnegative radiusBound 2) circulationNonnegative
  have centerBound : comparison.velocityCentroidCorrectionCenterEnvelope distance ≤
      12 * circulation * sourceScale ^ 2 * distance⁻¹ ^ 4 *
        (receiverScale * receiverState + sourceScale * sourceState) := by
    unfold velocityCentroidCorrectionCenterEnvelope
    have scalar := mul_le_mul_of_nonneg_left fourthMoment
      (show 0 ≤ 12 * distance⁻¹ ^ 4 by positivity)
    have actual := mul_le_mul scalar displacementBound (norm_nonneg _) (by positivity)
    convert actual using 1 <;> ring
  have inverseCube : actualDistance⁻¹ ^ 3 ≤ distance⁻¹ ^ 3 :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ distancePositive separated) 3
  have scalarBound : 96 * constant / (2 * Real.pi) ≤ 96 * constant :=
    div_le_self (by positivity) (by linarith [Real.pi_gt_three])
  have shapeIdentity : comparison.velocityCentroidCorrectionShapeEnvelope constant =
      (96 * constant / (2 * Real.pi)) *
        (|comparison.density| * comparison.first.radius ^ 2) * comparison.first.radius ^ 2 *
          actualDistance⁻¹ ^ 3 * comparison.spectralDifferenceBudget := by
    unfold velocityCentroidCorrectionShapeEnvelope
    change constant * 96 * ((|comparison.density| * comparison.first.radius ^ 2) /
      (2 * Real.pi * actualDistance)) * (comparison.first.radius / actualDistance) ^ 2 * _ = _
    ring
  have shapeBoundActual : comparison.velocityCentroidCorrectionShapeEnvelope constant ≤
      96 * constant * circulation * sourceScale ^ 2 * distance⁻¹ ^ 3 * sourceState := by
    rw [shapeIdentity]
    have radiusSquared := pow_le_pow_left₀ radiusNonnegative radiusBound 2
    have budgetNonnegative := comparison.spectralDifferenceBudget_nonnegative
    gcongr
  apply (div_le_div_of_nonneg_right (add_le_add centerBound shapeBoundActual) receiverPositive.le).trans_eq
  field_simp
  <;> ring

end EulerNonuniqueness.Paper.MovingPatchSourceComparison
