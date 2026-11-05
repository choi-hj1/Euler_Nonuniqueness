import EulerNonuniqueness.Section6.MovingQuadrupoleVelocityDecomposition

noncomputable section

open Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

def quadrupoleVelocityPointDifferenceEnvelope (comparison : MovingPatchFamilySourceComparison 4)
    (circulation : ℝ) (firstCenter secondCenter : ℂ) (radius distance : ℝ) : ℝ :=
  |circulation / (2 * Real.pi)| *
    (distance⁻¹ ^ 2 *
      ‖Section6.fourPointSignedMoment (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter) -
        Section6.fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)‖ +
      2 * distance⁻¹ ^ 3 * radius * ∑ patch : Fin 4,
        ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
          ((comparison.second.patch patch).center comparison.time - secondCenter)‖) +
  |circulation / (2 * Real.pi)| *
    (2 * distance⁻¹ ^ 3 *
      ‖Section6.fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)‖ +
      6 * distance⁻¹ ^ 4 * radius * ∑ patch : Fin 4,
        ‖(comparison.second.patch patch).center comparison.time - secondCenter‖) *
    ‖(comparison.firstReceiver comparison.time - firstCenter) -
      (comparison.secondReceiver comparison.time - secondCenter)‖

theorem quadrupoleVelocity_exists_centered_relative_bound :
    ∃ radius > (0 : ℝ), ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ comparison : MovingPatchFamilySourceComparison 4, ∀ circulation : ℝ,
      (∀ patch, comparison.first.density patch *
        volume.real ((comparison.first.patch patch).domain comparison.time) =
          circulation * Section6.fourPointSign patch) →
      (∀ patch, comparison.initial patch ∈ ball 0 radius) →
      (∀ patch, comparison.final patch ∈ ball 0 radius) →
      (∀ patch, contourCentroidFunctional ((comparison.first.patch patch).shape comparison.time) = 0) →
      (∀ patch, contourCentroidFunctional ((comparison.second.patch patch).shape comparison.time) = 0) →
      (∀ patch, (comparison.first.patch patch).center comparison.time =
        (comparison.first.patch patch).centroid comparison.time) →
      ∀ firstCenter secondCenter : ℂ, ∀ sourceRadius travel distance : ℝ,
      0 ≤ sourceRadius → 0 ≤ travel → 0 < distance →
      sourceRadius + travel + distance ≤ ‖comparison.firstReceiver comparison.time - firstCenter‖ →
      (∀ patch, ‖(comparison.first.patch patch).center comparison.time - firstCenter‖ ≤ sourceRadius) →
      (∀ patch, ‖(comparison.second.patch patch).center comparison.time - secondCenter‖ ≤ sourceRadius) →
      ‖(comparison.secondReceiver comparison.time - secondCenter) -
        (comparison.firstReceiver comparison.time - firstCenter)‖ ≤ travel →
      ∀ patchDistance patchTravel : Fin 4 → ℝ,
      (∀ patch, 0 < patchDistance patch) → (∀ patch, 0 ≤ patchTravel patch) →
      (∀ patch, 2 * (comparison.first.patch patch).radius + patchTravel patch + patchDistance patch ≤
        ‖comparison.firstReceiver comparison.time - (comparison.first.patch patch).center comparison.time‖) →
      (∀ patch, 2 * (comparison.first.patch patch).radius + patchDistance patch ≤
        ‖comparison.secondReceiver comparison.time - (comparison.second.patch patch).center comparison.time‖) →
      (∀ patch, ‖(comparison.source patch).displacementDifference‖ ≤ patchTravel patch) →
      (∀ patch, (comparison.first.patch patch).radius /
        ‖comparison.secondReceiver comparison.time - (comparison.second.patch patch).center comparison.time‖ ≤ parameterRadius) →
      ‖biotSavart (comparison.first.vorticity comparison.time) (comparison.firstReceiver comparison.time) -
        biotSavart (comparison.second.vorticity comparison.time) (comparison.secondReceiver comparison.time)‖ ≤
      comparison.quadrupoleVelocityPointDifferenceEnvelope circulation firstCenter secondCenter sourceRadius distance +
        ∑ patch : Fin 4, ((comparison.source patch).velocityCentroidCorrectionCenterEnvelope (patchDistance patch) +
          (comparison.source patch).velocityCentroidCorrectionShapeEnvelope constant) := by
  obtain ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, bound⟩ :=
    MovingPatchSourceComparison.velocityCentroidCorrection_exists_centered_relative_bound
  refine ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, ?_⟩
  intro comparison circulation masses initialInside finalInside firstCentered secondCentered trueCenter
    firstCenter secondCenter sourceRadius travel distance radiusNonnegative travelNonnegative positive separated
    firstPositionBound secondPositionBound receiverDifference patchDistance patchTravel patchPositive
    patchTravelNonnegative firstSeparated secondSeparated patchTravelBound small
  have pointBound := Section6.fourPointExternalPointVelocity_full_relative_bound
    (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter)
    (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)
    (comparison.firstReceiver comparison.time - firstCenter)
    (comparison.secondReceiver comparison.time - secondCenter) (circulation / (2 * Real.pi))
    radiusNonnegative travelNonnegative positive separated firstPositionBound secondPositionBound receiverDifference
  have correctionBound (patch : Fin 4) := bound (comparison.source patch)
    (initialInside patch) (finalInside patch) (firstCentered patch) (secondCentered patch) (trueCenter patch)
    (patchDistance patch) (patchTravel patch) (patchPositive patch) (patchTravelNonnegative patch)
    (firstSeparated patch) (secondSeparated patch) (patchTravelBound patch) (small patch)
  rw [comparison.quadrupoleVelocity_difference_eq_point_and_corrections circulation firstCenter secondCenter masses]
  exact (norm_add_le _ _).trans (add_le_add pointBound
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun patch _ => correctionBound patch)))

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
