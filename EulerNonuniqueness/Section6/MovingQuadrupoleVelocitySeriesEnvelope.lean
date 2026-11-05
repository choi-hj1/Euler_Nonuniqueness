import EulerNonuniqueness.Section6.MovingQuadrupoleRelativeSeries
import EulerNonuniqueness.Section6.MovingQuadrupoleVelocityRelative

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem velocity_envelope_le_zero_radius_series_envelope
    (comparison : MovingPatchFamilySourceComparison 4)
    (circulation : ℝ) (firstCenter secondCenter : ℂ)
    {sourceExtent distance constant : ℝ}
    (extentNonnegative : 0 ≤ sourceExtent) (distancePositive : 0 < distance)
    (constantNonnegative : 0 ≤ constant)
    (patchDistanceUpper : ∀ patch, ‖(comparison.source patch).secondReceiver -
      (comparison.source patch).second.center comparison.time‖ ≤ 16 * distance) :
    let virtual : MovingPatchFamilySourceComparison 4 :=
      {comparison with receiverRadius := 0, receiverRadius_nonnegative := le_rfl}
    comparison.quadrupoleVelocityPointDifferenceEnvelope circulation firstCenter secondCenter sourceExtent distance +
      ∑ patch : Fin 4, ((comparison.source patch).velocityCentroidCorrectionCenterEnvelope distance +
        (comparison.source patch).velocityCentroidCorrectionShapeEnvelope constant) ≤
      distance * (virtual.quadrupolePointDifferenceEnvelope circulation firstCenter secondCenter sourceExtent distance 96 +
        2 * ∑ patch : Fin 4, ((virtual.source patch).centroidCorrectionCenterEnvelope distance 96 +
          (virtual.source patch).centeredShapeDifferenceEnvelope constant 96)) := by
  dsimp only
  let virtual : MovingPatchFamilySourceComparison 4 :=
    {comparison with receiverRadius := 0, receiverRadius_nonnegative := le_rfl}
  let coefficient := |circulation| / (2 * Real.pi)
  let momentDifference := ‖fourPointSignedMoment (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter) -
    fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)‖
  let centeredDifference := ∑ patch : Fin 4, ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
    ((comparison.second.patch patch).center comparison.time - secondCenter)‖
  let secondMoment := ‖fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)‖
  let secondPositions := ∑ patch : Fin 4, ‖(comparison.second.patch patch).center comparison.time - secondCenter‖
  let displacement := ‖(comparison.firstReceiver comparison.time - firstCenter) -
    (comparison.secondReceiver comparison.time - secondCenter)‖
  let momentTerm := distance⁻¹ ^ 2 * momentDifference
  let centeredTerm := distance⁻¹ ^ 3 * sourceExtent * centeredDifference
  let translationTerm := distance⁻¹ ^ 3 * secondMoment * displacement
  let extentTerm := distance⁻¹ ^ 4 * sourceExtent * secondPositions * displacement
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have momentNonnegative : 0 ≤ momentTerm := by dsimp only [momentTerm, momentDifference]; positivity
  have centeredNonnegative : 0 ≤ centeredTerm := by dsimp only [centeredTerm, centeredDifference]; positivity
  have translationNonnegative : 0 ≤ translationTerm := by dsimp only [translationTerm, secondMoment, displacement]; positivity
  have extentTermNonnegative : 0 ≤ extentTerm := by dsimp only [extentTerm, secondPositions, displacement]; positivity
  have velocityIdentity : comparison.quadrupoleVelocityPointDifferenceEnvelope circulation firstCenter secondCenter sourceExtent distance =
      coefficient * (momentTerm + 2 * centeredTerm + 2 * translationTerm + 6 * extentTerm) := by
    dsimp only [quadrupoleVelocityPointDifferenceEnvelope, coefficient, momentTerm, momentDifference,
      centeredTerm, centeredDifference, translationTerm, secondMoment, extentTerm, secondPositions, displacement]
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    ring
  have seriesIdentity : distance * virtual.quadrupolePointDifferenceEnvelope circulation firstCenter secondCenter sourceExtent distance 96 =
      coefficient * (384 * momentTerm + 3072 * centeredTerm + 3072 * translationTerm + 49152 * extentTerm) := by
    dsimp only [quadrupolePointDifferenceEnvelope, virtual, coefficient, momentTerm, momentDifference,
      centeredTerm, centeredDifference, translationTerm, secondMoment, extentTerm, secondPositions, displacement]
    simp only [mul_zero, zero_div, sub_zero, inv_one, mul_one]
    field_simp [distancePositive.ne']; ring
  have pointBound : comparison.quadrupoleVelocityPointDifferenceEnvelope circulation firstCenter secondCenter sourceExtent distance ≤
      distance * virtual.quadrupolePointDifferenceEnvelope circulation firstCenter secondCenter sourceExtent distance 96 := by
    rw [velocityIdentity, seriesIdentity]
    apply mul_le_mul_of_nonneg_left _ coefficientNonnegative
    linarith only [momentNonnegative, centeredNonnegative, translationNonnegative, extentTermNonnegative]
  have centerBound (patch : Fin 4) :
      (comparison.source patch).velocityCentroidCorrectionCenterEnvelope distance ≤
        distance * (virtual.source patch).centroidCorrectionCenterEnvelope distance 96 := by
    let value := |(comparison.source patch).density| * (comparison.source patch).first.radius ^ 4 *
      distance⁻¹ ^ 4 * ‖(comparison.source patch).displacementDifference‖
    have valueNonnegative : 0 ≤ value := by dsimp only [value]; positivity
    have velocity : (comparison.source patch).velocityCentroidCorrectionCenterEnvelope distance = 12 * value := by
      dsimp only [MovingPatchSourceComparison.velocityCentroidCorrectionCenterEnvelope, value]
      ring
    have series : distance * (virtual.source patch).centroidCorrectionCenterEnvelope distance 96 = 98304 * value := by
      dsimp only [MovingPatchSourceComparison.centroidCorrectionCenterEnvelope, source, virtual, value,
        MovingPatchSourceComparison.displacementDifference]
      field_simp [distancePositive.ne']; ring
    rw [velocity, series]
    linarith only [valueNonnegative]
  have shapeBound (patch : Fin 4) :
      (comparison.source patch).velocityCentroidCorrectionShapeEnvelope constant ≤
        distance * (virtual.source patch).centeredShapeDifferenceEnvelope constant 96 := by
    let patchDistance := ‖(comparison.source patch).secondReceiver -
      (comparison.source patch).second.center comparison.time‖
    have patchDistanceNonnegative : 0 ≤ patchDistance := norm_nonneg _
    have seriesNonnegative : 0 ≤ (virtual.source patch).centeredShapeDifferenceEnvelope constant 96 := by
      dsimp only [MovingPatchSourceComparison.centeredShapeDifferenceEnvelope]
      exact mul_nonneg (by positivity) (virtual.source patch).spectralDifferenceBudget_nonnegative
    have identity : (comparison.source patch).velocityCentroidCorrectionShapeEnvelope constant =
        (patchDistance / 9216) * (virtual.source patch).centeredShapeDifferenceEnvelope constant 96 := by
      by_cases zeroDistance : patchDistance = 0
      · change ‖(comparison.source patch).secondReceiver -
          (comparison.source patch).second.center comparison.time‖ = 0 at zeroDistance
        dsimp only [MovingPatchSourceComparison.velocityCentroidCorrectionShapeEnvelope,
          MovingPatchSourceComparison.centeredShapeDifferenceEnvelope, source, virtual, patchDistance,
          MovingPatchSourceComparison.spectralDifferenceBudget]
        dsimp only [source] at zeroDistance
        rw [zeroDistance]
        norm_num
      · dsimp only [MovingPatchSourceComparison.velocityCentroidCorrectionShapeEnvelope,
          MovingPatchSourceComparison.centeredShapeDifferenceEnvelope, source, virtual, patchDistance,
          MovingPatchSourceComparison.spectralDifferenceBudget]
        have nonzero : ‖(comparison.source patch).secondReceiver -
          (comparison.source patch).second.center comparison.time‖ ≠ 0 := zeroDistance
        dsimp only [source] at nonzero
        field_simp [nonzero]; ring
    rw [identity]
    apply mul_le_mul_of_nonneg_right _ seriesNonnegative
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 9216)).mpr
    have upper : patchDistance ≤ 16 * distance := patchDistanceUpper patch
    linarith only [upper, distancePositive]
  have correctionsBound := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ =>
    add_le_add (centerBound patch) (shapeBound patch))
  simp only [← mul_add, ← Finset.mul_sum] at correctionsBound
  have correctionsNonnegative : 0 ≤ ∑ patch : Fin 4,
      ((virtual.source patch).centroidCorrectionCenterEnvelope distance 96 +
        (virtual.source patch).centeredShapeDifferenceEnvelope constant 96) := by
    apply Finset.sum_nonneg
    intro patch _
    apply add_nonneg
    · dsimp only [MovingPatchSourceComparison.centroidCorrectionCenterEnvelope]
      positivity
    · dsimp only [MovingPatchSourceComparison.centeredShapeDifferenceEnvelope]
      exact mul_nonneg (by positivity) (virtual.source patch).spectralDifferenceBudget_nonnegative
  apply (add_le_add pointBound correctionsBound).trans
  nlinarith only [mul_nonneg distancePositive.le correctionsNonnegative]

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
