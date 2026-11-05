import EulerNonuniqueness.Section6.MovingPatchSourceCentroidDecomposition

noncomputable section

open Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingPatchSourceComparison

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

def centroidCorrectionCenterEnvelope (comparison : MovingPatchSourceComparison) (distance weight : ℝ) : ℝ :=
  1024 * weight * |comparison.density| * comparison.first.radius ^ 4 * distance⁻¹ ^ 5 *
    ‖comparison.displacementDifference‖

theorem centroidCorrection_exists_centered_weighted_relative_series :
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
      ∀ weight : ℝ, 0 ≤ weight →
      8 * weight * comparison.receiverRadius / distance < 1 →
      96 * weight * comparison.receiverRadius / ‖comparison.secondReceiver - comparison.second.center comparison.time‖ < 1 →
      Summable (fun power : ℕ => weight ^ (power + 1) * ‖comparison.centroidCorrectionDifference power‖) ∧
        (∑' power : ℕ, weight ^ (power + 1) * ‖comparison.centroidCorrectionDifference power‖) ≤
          comparison.centroidCorrectionCenterEnvelope distance weight *
              (1 - 8 * weight * comparison.receiverRadius / distance)⁻¹ +
            comparison.centeredShapeDifferenceEnvelope constant weight *
              (1 - 96 * weight * comparison.receiverRadius /
                ‖comparison.secondReceiver - comparison.second.center comparison.time‖)⁻¹ := by
  obtain ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, bound⟩ :=
    MovingMaterialPatch.sourceTaylorCoefficient_exists_centered_spectral_shape_bound
  refine ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, ?_⟩
  intro comparison initialInside finalInside firstCentered secondCentered trueCenter distance travel positive travelNonnegative
    firstSeparated secondSeparated travelBound small weight weightNonnegative firstRatioSmall secondRatioSmall
  have receiverNonnegative := comparison.receiverRadius_nonnegative
  have actualShape := bound comparison.first comparison.second comparison.density comparison.hybridReceiver
    comparison.secondReceiver comparison.receiverRadius comparison.receiverRadius_nonnegative comparison.time
    comparison.initial comparison.final initialInside finalInside comparison.firstShape comparison.secondShape
    comparison.radiusEqual comparison.phaseEqual comparison.hybridReceiver_displacement
    comparison.firstArea comparison.secondArea firstCentered secondCentered distance positive
    (by simpa only [comparison.hybridReceiver_displacement] using secondSeparated)
    (by simpa only [comparison.hybridReceiver_displacement] using small)
  have shapeBound (power : ℕ) : weight ^ (power + 1) *
      ‖comparison.first.sourceTaylorCentroidCorrection comparison.density comparison.hybridReceiver
          comparison.receiverRadius power comparison.time -
        comparison.second.sourceTaylorCentroidCorrection comparison.density comparison.secondReceiver
          comparison.receiverRadius power comparison.time‖ ≤
      comparison.centeredShapeDifferenceEnvelope constant weight *
        (96 * weight * comparison.receiverRadius /
          ‖comparison.secondReceiver - comparison.second.center comparison.time‖) ^ power := by
    rw [comparison.hybrid_centroidCorrectionDifference_eq_shapeDifference]
    have estimate := actualShape power
    simp only [comparison.hybridReceiver_displacement] at estimate
    apply (mul_le_mul_of_nonneg_left estimate (pow_nonneg weightNonnegative (power + 1))).trans_eq
    dsimp only [centeredShapeDifferenceEnvelope, spectralDifferenceBudget]
    simp only [pow_add, pow_succ, div_pow, mul_pow]
    ring
  have hybridTravel : ‖comparison.hybridReceiver - comparison.firstReceiver‖ ≤ travel := by
    rw [norm_sub_rev, comparison.firstReceiver_sub_hybridReceiver]
    exact travelBound
  have centerBound (power : ℕ) : weight ^ (power + 1) *
      ‖comparison.first.sourceTaylorCentroidCorrection comparison.density comparison.firstReceiver
          comparison.receiverRadius power comparison.time -
        comparison.first.sourceTaylorCentroidCorrection comparison.density comparison.hybridReceiver
          comparison.receiverRadius power comparison.time‖ ≤
      comparison.centroidCorrectionCenterEnvelope distance weight *
        (8 * weight * comparison.receiverRadius / distance) ^ power := by
    have actual := comparison.first.sourceTaylorCentroidCorrection_receiver_weighted_term_le
      comparison.density comparison.firstReceiver comparison.firstReceiver comparison.hybridReceiver power comparison.time
      comparison.receiverRadius_nonnegative travelNonnegative positive weightNonnegative trueCenter comparison.firstArea
      firstSeparated (by simpa using travelNonnegative) hybridTravel
    simpa only [centroidCorrectionCenterEnvelope, comparison.firstReceiver_sub_hybridReceiver] using actual
  have pointwise (power : ℕ) : weight ^ (power + 1) * ‖comparison.centroidCorrectionDifference power‖ ≤
      comparison.centroidCorrectionCenterEnvelope distance weight *
          (8 * weight * comparison.receiverRadius / distance) ^ power +
        comparison.centeredShapeDifferenceEnvelope constant weight *
          (96 * weight * comparison.receiverRadius /
            ‖comparison.secondReceiver - comparison.second.center comparison.time‖) ^ power := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub
      (comparison.first.sourceTaylorCentroidCorrection comparison.density comparison.firstReceiver comparison.receiverRadius power comparison.time)
      (comparison.first.sourceTaylorCentroidCorrection comparison.density comparison.hybridReceiver comparison.receiverRadius power comparison.time)
      (comparison.second.sourceTaylorCentroidCorrection comparison.density comparison.secondReceiver comparison.receiverRadius power comparison.time)
    exact (mul_le_mul_of_nonneg_left triangle (pow_nonneg weightNonnegative (power + 1))).trans
      (by rw [mul_add]; exact add_le_add (centerBound power) (shapeBound power))
  exact EulerNonuniqueness.General.summable_and_tsum_le_of_two_geometric_majorants
    (fun power : ℕ => weight ^ (power + 1) * ‖comparison.centroidCorrectionDifference power‖)
    (comparison.centroidCorrectionCenterEnvelope distance weight) (comparison.centeredShapeDifferenceEnvelope constant weight)
    (8 * weight * comparison.receiverRadius / distance)
    (96 * weight * comparison.receiverRadius / ‖comparison.secondReceiver - comparison.second.center comparison.time‖)
    (fun power => by positivity) (by positivity) firstRatioSmall (by positivity) secondRatioSmall pointwise

end EulerNonuniqueness.Paper.MovingPatchSourceComparison
