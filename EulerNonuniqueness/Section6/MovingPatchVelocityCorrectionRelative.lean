import EulerNonuniqueness.Section6.MovingPatchVelocityShapeDifference
import EulerNonuniqueness.Section6.MovingPatchSourceComparison

noncomputable section

open Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingPatchSourceComparison

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

def velocityCentroidCorrectionDifference (comparison : MovingPatchSourceComparison) : ℂ :=
  comparison.first.sourceVelocityCentroidCorrection comparison.density comparison.firstReceiver comparison.time -
    comparison.second.sourceVelocityCentroidCorrection comparison.density comparison.secondReceiver comparison.time

def velocityCentroidCorrectionCenterEnvelope (comparison : MovingPatchSourceComparison) (distance : ℝ) : ℝ :=
  12 * |comparison.density| * comparison.first.radius ^ 4 * distance⁻¹ ^ 4 *
    ‖comparison.displacementDifference‖

def velocityCentroidCorrectionShapeEnvelope (comparison : MovingPatchSourceComparison) (constant : ℝ) : ℝ :=
  constant * 96 *
    (|comparison.density| * comparison.first.radius ^ 2 /
      (2 * Real.pi * ‖comparison.secondReceiver - comparison.second.center comparison.time‖)) *
    (comparison.first.radius / ‖comparison.secondReceiver - comparison.second.center comparison.time‖) ^ 2 *
    comparison.spectralDifferenceBudget

theorem velocityCentroidCorrection_exists_centered_relative_bound :
    ∃ radius > (0 : ℝ), ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ comparison : MovingPatchSourceComparison,
      comparison.initial ∈ ball 0 radius → comparison.final ∈ ball 0 radius →
      contourCentroidFunctional (comparison.first.shape comparison.time) = 0 →
      contourCentroidFunctional (comparison.second.shape comparison.time) = 0 →
      comparison.first.center comparison.time = comparison.first.centroid comparison.time →
      ∀ distance travel : ℝ, 0 < distance → 0 ≤ travel →
      2 * comparison.first.radius + travel + distance ≤
        ‖comparison.firstReceiver - comparison.first.center comparison.time‖ →
      2 * comparison.first.radius + distance ≤
        ‖comparison.secondReceiver - comparison.second.center comparison.time‖ →
      ‖comparison.displacementDifference‖ ≤ travel →
      comparison.first.radius / ‖comparison.secondReceiver - comparison.second.center comparison.time‖ ≤ parameterRadius →
      ‖comparison.velocityCentroidCorrectionDifference‖ ≤
        comparison.velocityCentroidCorrectionCenterEnvelope distance +
          comparison.velocityCentroidCorrectionShapeEnvelope constant := by
  obtain ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, bound⟩ :=
    MovingMaterialPatch.sourceVelocityCentroidCorrection_exists_spectral_shape_bound
  refine ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, ?_⟩
  intro comparison initialInside finalInside firstCentered secondCentered trueCenter distance travel positive
    travelNonnegative firstSeparated secondSeparated travelBound small
  have actualShape := bound comparison.first comparison.second comparison.density comparison.hybridReceiver
    comparison.secondReceiver comparison.time comparison.initial comparison.final initialInside finalInside
    comparison.firstShape comparison.secondShape comparison.radiusEqual comparison.phaseEqual
    comparison.hybridReceiver_displacement comparison.firstArea comparison.secondArea firstCentered secondCentered
    distance positive (by simpa only [comparison.hybridReceiver_displacement] using secondSeparated)
    (by simpa only [comparison.hybridReceiver_displacement] using small)
  have hybridTravel : ‖comparison.hybridReceiver - comparison.firstReceiver‖ ≤ travel := by
    rw [norm_sub_rev, comparison.firstReceiver_sub_hybridReceiver]
    exact travelBound
  have actualCenter := comparison.first.sourceVelocityCentroidCorrection_receiver_difference_norm_le
    comparison.density comparison.firstReceiver comparison.firstReceiver comparison.hybridReceiver comparison.time
    travelNonnegative positive trueCenter comparison.firstArea firstSeparated
    (by simpa using travelNonnegative) hybridTravel
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (comparison.first.sourceVelocityCentroidCorrection comparison.density comparison.firstReceiver comparison.time)
    (comparison.first.sourceVelocityCentroidCorrection comparison.density comparison.hybridReceiver comparison.time)
    (comparison.second.sourceVelocityCentroidCorrection comparison.density comparison.secondReceiver comparison.time)
  apply triangle.trans
  exact (add_le_add actualCenter actualShape).trans_eq (by
    simp only [velocityCentroidCorrectionDifference, velocityCentroidCorrectionCenterEnvelope,
      velocityCentroidCorrectionShapeEnvelope, spectralDifferenceBudget,
      comparison.hybridReceiver_displacement, comparison.firstReceiver_sub_hybridReceiver])

end EulerNonuniqueness.Paper.MovingPatchSourceComparison
