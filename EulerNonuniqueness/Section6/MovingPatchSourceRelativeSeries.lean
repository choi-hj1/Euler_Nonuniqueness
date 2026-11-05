import EulerNonuniqueness.Section6.MovingPatchSourceComparison
import EulerNonuniqueness.General.TwoGeometricMajorants

noncomputable section

open Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingPatchSourceComparison

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

def coefficientDifference (comparison : MovingPatchSourceComparison) (power : ℕ) : ℂ :=
  comparison.first.sourceTaylorCoefficient comparison.density comparison.firstReceiver comparison.receiverRadius power comparison.time -
    comparison.second.sourceTaylorCoefficient comparison.density comparison.secondReceiver comparison.receiverRadius power comparison.time

def centerDifferenceEnvelope (comparison : MovingPatchSourceComparison) (distance weight : ℝ) : ℝ :=
  4 * weight * ((distance⁻¹ ^ 3 * ‖comparison.displacementDifference‖ *
    (|comparison.density| * Real.pi * comparison.first.radius ^ 2)) / (2 * Real.pi))

def shapeDifferenceEnvelope (comparison : MovingPatchSourceComparison) (constant weight : ℝ) : ℝ :=
  constant * (96 : ℝ) ^ 2 * weight *
    (|comparison.density| * comparison.first.radius ^ 2 /
      (2 * Real.pi * ‖comparison.secondReceiver - comparison.second.center comparison.time‖ ^ 2)) *
    (comparison.first.radius / ‖comparison.secondReceiver - comparison.second.center comparison.time‖) *
    comparison.spectralDifferenceBudget

theorem sourceCoefficient_exists_geometric_relative_bound :
    ∃ radius > (0 : ℝ), ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ comparison : MovingPatchSourceComparison,
      comparison.initial ∈ ball 0 radius → comparison.final ∈ ball 0 radius →
      ∀ distance : ℝ, 0 < distance →
      2 * comparison.first.radius + distance ≤ ‖comparison.firstReceiver - comparison.first.center comparison.time‖ →
      2 * comparison.first.radius + distance ≤ ‖comparison.secondReceiver - comparison.second.center comparison.time‖ →
      comparison.first.radius / ‖comparison.secondReceiver - comparison.second.center comparison.time‖ ≤ parameterRadius →
      ∀ weight : ℝ, 0 ≤ weight → ∀ power : ℕ,
      weight ^ (power + 1) * ‖comparison.coefficientDifference power‖ ≤
        comparison.centerDifferenceEnvelope distance weight * (2 * weight * comparison.receiverRadius / distance) ^ power +
        comparison.shapeDifferenceEnvelope constant weight *
          (96 * weight * comparison.receiverRadius /
            ‖comparison.secondReceiver - comparison.second.center comparison.time‖) ^ power := by
  obtain ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, bound⟩ :=
    MovingMaterialPatch.sourceTaylorCoefficient_exists_spectral_shape_bound
  refine ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, ?_⟩
  intro comparison initialInside finalInside distance positive firstSeparated secondSeparated small weight weightNonnegative power
  have centerBound := comparison.sourceTaylorCoefficient_center_weighted_term_le positive weightNonnegative
    firstSeparated secondSeparated power
  have actualShape := bound comparison.first comparison.second comparison.density comparison.hybridReceiver
    comparison.secondReceiver comparison.receiverRadius comparison.receiverRadius_nonnegative comparison.time
    comparison.initial comparison.final initialInside finalInside comparison.firstShape comparison.secondShape
    comparison.radiusEqual comparison.phaseEqual comparison.hybridReceiver_displacement
    comparison.firstArea comparison.secondArea distance positive
    (by simpa only [comparison.hybridReceiver_displacement] using secondSeparated)
    (by simpa only [comparison.hybridReceiver_displacement] using small) power
  simp only [comparison.hybridReceiver_displacement] at actualShape
  have shapeBound : weight ^ (power + 1) *
      ‖comparison.first.sourceTaylorCoefficient comparison.density comparison.hybridReceiver comparison.receiverRadius power comparison.time -
        comparison.second.sourceTaylorCoefficient comparison.density comparison.secondReceiver comparison.receiverRadius power comparison.time‖ ≤
      comparison.shapeDifferenceEnvelope constant weight *
        (96 * weight * comparison.receiverRadius /
          ‖comparison.secondReceiver - comparison.second.center comparison.time‖) ^ power := by
    apply (mul_le_mul_of_nonneg_left actualShape (pow_nonneg weightNonnegative (power + 1))).trans_eq
    dsimp only [shapeDifferenceEnvelope, spectralDifferenceBudget]
    simp only [pow_add, pow_succ, div_pow, mul_pow]
    ring
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (comparison.first.sourceTaylorCoefficient comparison.density comparison.firstReceiver comparison.receiverRadius power comparison.time)
    (comparison.first.sourceTaylorCoefficient comparison.density comparison.hybridReceiver comparison.receiverRadius power comparison.time)
    (comparison.second.sourceTaylorCoefficient comparison.density comparison.secondReceiver comparison.receiverRadius power comparison.time)
  exact (mul_le_mul_of_nonneg_left triangle (pow_nonneg weightNonnegative (power + 1))).trans
    ((by rw [mul_add]; exact add_le_add centerBound shapeBound))

theorem sourceCoefficient_exists_weighted_relative_series :
    ∃ radius > (0 : ℝ), ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ comparison : MovingPatchSourceComparison,
      comparison.initial ∈ ball 0 radius → comparison.final ∈ ball 0 radius →
      ∀ distance : ℝ, 0 < distance →
      2 * comparison.first.radius + distance ≤ ‖comparison.firstReceiver - comparison.first.center comparison.time‖ →
      2 * comparison.first.radius + distance ≤ ‖comparison.secondReceiver - comparison.second.center comparison.time‖ →
      comparison.first.radius / ‖comparison.secondReceiver - comparison.second.center comparison.time‖ ≤ parameterRadius →
      ∀ weight : ℝ, 0 ≤ weight →
      2 * weight * comparison.receiverRadius / distance < 1 →
      96 * weight * comparison.receiverRadius / ‖comparison.secondReceiver - comparison.second.center comparison.time‖ < 1 →
      Summable (fun power : ℕ => weight ^ (power + 1) * ‖comparison.coefficientDifference power‖) ∧
        (∑' power : ℕ, weight ^ (power + 1) * ‖comparison.coefficientDifference power‖) ≤
          comparison.centerDifferenceEnvelope distance weight * (1 - 2 * weight * comparison.receiverRadius / distance)⁻¹ +
          comparison.shapeDifferenceEnvelope constant weight *
            (1 - 96 * weight * comparison.receiverRadius /
              ‖comparison.secondReceiver - comparison.second.center comparison.time‖)⁻¹ := by
  obtain ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, bound⟩ :=
    sourceCoefficient_exists_geometric_relative_bound
  refine ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, ?_⟩
  intro comparison initialInside finalInside distance positive firstSeparated secondSeparated small weight weightNonnegative
    firstRatioSmall secondRatioSmall
  have receiverNonnegative := comparison.receiverRadius_nonnegative
  exact EulerNonuniqueness.General.summable_and_tsum_le_of_two_geometric_majorants
    (fun power : ℕ => weight ^ (power + 1) * ‖comparison.coefficientDifference power‖)
    (comparison.centerDifferenceEnvelope distance weight) (comparison.shapeDifferenceEnvelope constant weight)
    (2 * weight * comparison.receiverRadius / distance)
    (96 * weight * comparison.receiverRadius / ‖comparison.secondReceiver - comparison.second.center comparison.time‖)
    (fun power => by positivity) (by positivity) firstRatioSmall (by positivity) secondRatioSmall
    (bound comparison initialInside finalInside distance positive firstSeparated secondSeparated small weight weightNonnegative)

end EulerNonuniqueness.Paper.MovingPatchSourceComparison
