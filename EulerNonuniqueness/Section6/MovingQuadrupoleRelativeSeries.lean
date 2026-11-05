import EulerNonuniqueness.Section6.MovingQuadrupoleRelativeCoefficient
import EulerNonuniqueness.General.WeightedFiniteCorrectionSeries

noncomputable section

open Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

def quadrupolePointDifferenceEnvelope (comparison : MovingPatchFamilySourceComparison 4)
    (circulation : ℝ) (firstCenter secondCenter : ℂ) (radius distance weight : ℝ) : ℝ :=
  (weight * (|circulation| / (2 * Real.pi)) *
    (4 * distance⁻¹ ^ 3 *
      ‖Section6.fourPointSignedMoment (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter) -
        Section6.fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)‖ +
      32 * distance⁻¹ ^ 4 * radius *
        ∑ patch : Fin 4, ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
          ((comparison.second.patch patch).center comparison.time - secondCenter)‖)) *
      (1 - 4 * weight * comparison.receiverRadius / distance)⁻¹ +
  (weight * (|circulation| / (2 * Real.pi)) *
    (32 * distance⁻¹ ^ 4 *
      ‖Section6.fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)‖ +
      512 * distance⁻¹ ^ 5 * radius *
        ∑ patch : Fin 4, ‖(comparison.second.patch patch).center comparison.time - secondCenter‖) *
      ‖(comparison.firstReceiver comparison.time - firstCenter) -
        (comparison.secondReceiver comparison.time - secondCenter)‖) *
      (1 - 8 * weight * comparison.receiverRadius / distance)⁻¹

theorem quadrupoleCoefficient_exists_centered_weighted_relative_series :
    ∃ cap > (0 : ℝ), ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ comparison : MovingPatchFamilySourceComparison 4,
      (∀ patch, comparison.initial patch ∈ ball 0 cap) →
      (∀ patch, comparison.final patch ∈ ball 0 cap) →
      (∀ patch, contourCentroidFunctional ((comparison.first.patch patch).shape comparison.time) = 0) →
      (∀ patch, contourCentroidFunctional ((comparison.second.patch patch).shape comparison.time) = 0) →
      (∀ patch, (comparison.first.patch patch).center comparison.time =
        (comparison.first.patch patch).centroid comparison.time) →
      ∀ circulation : ℝ, ∀ firstCenter secondCenter : ℂ,
      (∀ patch, comparison.first.density patch *
        volume.real ((comparison.first.patch patch).domain comparison.time) =
          circulation * Section6.fourPointSign patch) →
      ∀ radius travel distance weight : ℝ, ∀ patchTravel : Fin 4 → ℝ,
      0 ≤ radius → 0 ≤ travel → 0 < distance → 0 ≤ weight →
      radius + travel + distance ≤ ‖comparison.firstReceiver comparison.time - firstCenter‖ →
      (∀ patch, ‖(comparison.first.patch patch).center comparison.time - firstCenter‖ ≤ radius) →
      (∀ patch, ‖(comparison.second.patch patch).center comparison.time - secondCenter‖ ≤ radius) →
      ‖(comparison.secondReceiver comparison.time - secondCenter) -
        (comparison.firstReceiver comparison.time - firstCenter)‖ ≤ travel →
      (∀ patch, 0 ≤ patchTravel patch) →
      (∀ patch, 2 * (comparison.first.patch patch).radius + patchTravel patch + distance ≤
        ‖comparison.firstReceiver comparison.time - (comparison.first.patch patch).center comparison.time‖) →
      (∀ patch, 2 * (comparison.first.patch patch).radius + distance ≤
        ‖comparison.secondReceiver comparison.time - (comparison.second.patch patch).center comparison.time‖) →
      (∀ patch, ‖(comparison.source patch).displacementDifference‖ ≤ patchTravel patch) →
      (∀ patch, (comparison.first.patch patch).radius /
        ‖comparison.secondReceiver comparison.time - (comparison.second.patch patch).center comparison.time‖ ≤ parameterRadius) →
      4 * weight * comparison.receiverRadius / distance < 1 →
      8 * weight * comparison.receiverRadius / distance < 1 →
      (∀ patch, 96 * weight * comparison.receiverRadius /
        ‖comparison.secondReceiver comparison.time - (comparison.second.patch patch).center comparison.time‖ < 1) →
      Summable (fun power : ℕ => weight ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient Finset.univ comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          comparison.second.exteriorTaylorCoefficient Finset.univ comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) ∧
      (∑' power : ℕ, weight ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient Finset.univ comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          comparison.second.exteriorTaylorCoefficient Finset.univ comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) ≤
        comparison.quadrupolePointDifferenceEnvelope circulation firstCenter secondCenter radius distance weight +
          ∑ patch : Fin 4, (
            (comparison.source patch).centroidCorrectionCenterEnvelope distance weight *
                (1 - 8 * weight * comparison.receiverRadius / distance)⁻¹ +
              (comparison.source patch).centeredShapeDifferenceEnvelope constant weight *
                (1 - 96 * weight * comparison.receiverRadius /
                  ‖comparison.secondReceiver comparison.time - (comparison.second.patch patch).center comparison.time‖)⁻¹) := by
  obtain ⟨cap, capPositive, parameterRadius, parameterPositive, constant, nonnegative, correctionBound⟩ :=
    MovingPatchSourceComparison.centroidCorrection_exists_centered_weighted_relative_series
  refine ⟨cap, capPositive, parameterRadius, parameterPositive, constant, nonnegative, ?_⟩
  intro comparison firstInside secondInside firstCentered secondCentered firstTrueCenter circulation
    firstCenter secondCenter masses radius travel distance weight patchTravel radiusNonnegative
    travelNonnegative positive weightNonnegative separated firstPositionBound secondPositionBound
    receiverDifference patchTravelNonnegative firstSeparated secondSeparated patchTravelBound
    small firstRatio secondRatio shapeRatio
  have pointBound := Section6.pointSourceTaylorCoefficient_full_relative_summable_and_tsum_le
    (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter)
    (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)
    (comparison.firstReceiver comparison.time - firstCenter)
    (comparison.secondReceiver comparison.time - secondCenter) circulation
    comparison.receiverRadius_nonnegative radiusNonnegative travelNonnegative positive weightNonnegative
    separated firstPositionBound secondPositionBound receiverDifference firstRatio secondRatio
  have corrections (patch : Fin 4) := correctionBound (comparison.source patch)
    (firstInside patch) (secondInside patch) (firstCentered patch) (secondCentered patch)
    (firstTrueCenter patch) distance (patchTravel patch) positive (patchTravelNonnegative patch)
    (firstSeparated patch) (secondSeparated patch) (patchTravelBound patch) (small patch)
    weight weightNonnegative secondRatio (shapeRatio patch)
  have assembled := EulerNonuniqueness.General.summable_weighted_norm_of_eq_add_finite_corrections
    Finset.univ (fun power => weight ^ (power + 1))
    (fun power => pow_nonneg weightNonnegative (power + 1))
    (fun power => comparison.first.exteriorTaylorCoefficient Finset.univ comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
      comparison.second.exteriorTaylorCoefficient Finset.univ comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time)
    (fun power => Section6.pointSourceTaylorCoefficient circulation comparison.receiverRadius
        (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter)
        (comparison.firstReceiver comparison.time - firstCenter) power -
      Section6.pointSourceTaylorCoefficient circulation comparison.receiverRadius
        (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)
        (comparison.secondReceiver comparison.time - secondCenter) power)
    (fun patch power => (comparison.source patch).centroidCorrectionDifference power)
    (fun power => by
      simpa using (comparison.quadrupoleCoefficient_difference_eq_point_and_corrections
        circulation firstCenter secondCenter power masses))
    pointBound.1 (fun patch _ => (corrections patch).1)
  refine ⟨assembled.1, assembled.2.trans ?_⟩
  apply add_le_add pointBound.2
  exact Finset.sum_le_sum (fun patch _ => (corrections patch).2)

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
