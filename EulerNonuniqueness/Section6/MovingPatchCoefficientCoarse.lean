import EulerNonuniqueness.Section6.MovingPatchCenteredSourceSeries
import EulerNonuniqueness.Section6.MovingPatchSourceCorrectionRelative

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchSourceComparison

set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem centroidCorrectionEnvelopes_coarse_bound (comparison : MovingPatchSourceComparison)
    {circulation constant distance weight receiverScale sourceScale receiverState sourceState : ℝ}
    (circulationNonnegative : 0 ≤ circulation) (constantNonnegative : 0 ≤ constant)
    (distancePositive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (receiverNonnegative : 0 ≤ receiverScale) (sourceNonnegative : 0 ≤ sourceScale)
    (receiverStateNonnegative : 0 ≤ receiverState) (sourceStateNonnegative : 0 ≤ sourceState)
    (massBound : |comparison.density| * comparison.first.radius ^ 2 ≤ circulation)
    (radiusBound : comparison.first.radius ≤ sourceScale)
    (separated : distance ≤ ‖comparison.secondReceiver - comparison.second.center comparison.time‖)
    (displacementBound : ‖comparison.displacementDifference‖ ≤ receiverScale * receiverState + sourceScale * sourceState)
    (shapeBound : comparison.spectralDifferenceBudget ≤ sourceState) :
    comparison.centroidCorrectionCenterEnvelope distance weight + comparison.centeredShapeDifferenceEnvelope constant weight ≤
      circulation * weight * (1024 * sourceScale ^ 3 / distance ^ 5 +
        9216 * constant * sourceScale ^ 2 / distance ^ 4) * sourceState +
      circulation * weight * (1024 * receiverScale * sourceScale ^ 2 / distance ^ 5) * receiverState := by
  let actualDistance := ‖comparison.secondReceiver - comparison.second.center comparison.time‖
  have actualPositive : 0 < actualDistance := distancePositive.trans_le separated
  have radiusNonnegative := comparison.first.radius_positive.le
  have fourthMoment : |comparison.density| * comparison.first.radius ^ 4 ≤ circulation * sourceScale ^ 2 := by
    calc
      _ = (|comparison.density| * comparison.first.radius ^ 2) * comparison.first.radius ^ 2 := by ring
      _ ≤ circulation * comparison.first.radius ^ 2 := mul_le_mul_of_nonneg_right massBound (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ radiusNonnegative radiusBound 2) circulationNonnegative
  have centerBound : comparison.centroidCorrectionCenterEnvelope distance weight ≤
      1024 * weight * circulation * sourceScale ^ 2 * distance⁻¹ ^ 5 *
        (receiverScale * receiverState + sourceScale * sourceState) := by
    unfold centroidCorrectionCenterEnvelope
    have scalar := mul_le_mul_of_nonneg_left fourthMoment (show 0 ≤ 1024 * weight * distance⁻¹ ^ 5 by positivity)
    have actual := mul_le_mul scalar displacementBound (norm_nonneg _) (by positivity)
    convert actual using 1 <;> ring
  have inverseFourth : actualDistance⁻¹ ^ 4 ≤ distance⁻¹ ^ 4 :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ distancePositive separated) 4
  have scalarBound : 9216 * constant * weight / (2 * Real.pi) ≤ 9216 * constant * weight :=
    div_le_self (by positivity) (by linarith [Real.pi_gt_three])
  have shapeIdentity : comparison.centeredShapeDifferenceEnvelope constant weight =
      (9216 * constant * weight / (2 * Real.pi)) *
        (|comparison.density| * comparison.first.radius ^ 2) * comparison.first.radius ^ 2 *
          actualDistance⁻¹ ^ 4 * comparison.spectralDifferenceBudget := by
    unfold centeredShapeDifferenceEnvelope
    change constant * 96 ^ 2 * weight * ((|comparison.density| * comparison.first.radius ^ 2) /
      (2 * Real.pi * actualDistance ^ 2)) * (comparison.first.radius / actualDistance) ^ 2 * _ = _
    ring
  have shapeBoundActual : comparison.centeredShapeDifferenceEnvelope constant weight ≤
      9216 * constant * weight * circulation * sourceScale ^ 2 * distance⁻¹ ^ 4 * sourceState := by
    rw [shapeIdentity]
    have radiusSquared := pow_le_pow_left₀ radiusNonnegative radiusBound 2
    have budgetNonnegative := comparison.spectralDifferenceBudget_nonnegative
    gcongr
  apply (add_le_add centerBound shapeBoundActual).trans_eq
  field_simp
  <;> ring

end EulerNonuniqueness.Paper.MovingPatchSourceComparison
