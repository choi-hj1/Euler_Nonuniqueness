import EulerNonuniqueness.Section6.MovingPatchFamilySourceComparison
import EulerNonuniqueness.Section6.MovingPatchCenteredSourceSeries

noncomputable section

open Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exteriorTaylorCoefficient_exists_centered_weighted_relative_series :
    ∃ radius > (0 : ℝ), ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ count : ℕ, ∀ comparison : MovingPatchFamilySourceComparison count, ∀ selected : Finset (Fin count),
      (∀ index ∈ selected, comparison.initial index ∈ ball 0 radius) →
      (∀ index ∈ selected, comparison.final index ∈ ball 0 radius) →
      (∀ index ∈ selected, contourCentroidFunctional ((comparison.first.patch index).shape comparison.time) = 0) →
      (∀ index ∈ selected, contourCentroidFunctional ((comparison.second.patch index).shape comparison.time) = 0) →
      ∀ distance : Fin count → ℝ, (∀ index ∈ selected, 0 < distance index) →
      (∀ index ∈ selected, 2 * (comparison.first.patch index).radius + distance index ≤
        ‖comparison.firstReceiver comparison.time - (comparison.first.patch index).center comparison.time‖) →
      (∀ index ∈ selected, 2 * (comparison.first.patch index).radius + distance index ≤
        ‖comparison.secondReceiver comparison.time - (comparison.second.patch index).center comparison.time‖) →
      (∀ index ∈ selected, (comparison.first.patch index).radius /
        ‖comparison.secondReceiver comparison.time - (comparison.second.patch index).center comparison.time‖ ≤ parameterRadius) →
      ∀ weight : ℝ, 0 ≤ weight →
      (∀ index ∈ selected, 2 * weight * comparison.receiverRadius / distance index < 1) →
      (∀ index ∈ selected, 96 * weight * comparison.receiverRadius /
        ‖comparison.secondReceiver comparison.time - (comparison.second.patch index).center comparison.time‖ < 1) →
      Summable (fun power : ℕ => weight ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          comparison.second.exteriorTaylorCoefficient selected comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) ∧
      (∑' power : ℕ, weight ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          comparison.second.exteriorTaylorCoefficient selected comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) ≤
        ∑ index ∈ selected, (
          (comparison.source index).centerDifferenceEnvelope (distance index) weight *
            (1 - 2 * weight * comparison.receiverRadius / distance index)⁻¹ +
          (comparison.source index).centeredShapeDifferenceEnvelope constant weight *
            (1 - 96 * weight * comparison.receiverRadius /
              ‖comparison.secondReceiver comparison.time - (comparison.second.patch index).center comparison.time‖)⁻¹) := by
  obtain ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, bound⟩ :=
    MovingPatchSourceComparison.sourceCoefficient_exists_centered_weighted_relative_series
  refine ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, ?_⟩
  intro count comparison selected initialInside finalInside firstCentered secondCentered distance positive firstSeparated secondSeparated small
    weight weightNonnegative firstRatioSmall secondRatioSmall
  have individual (index : Fin count) (member : index ∈ selected) :=
    bound (comparison.source index) (initialInside index member) (finalInside index member)
      (firstCentered index member) (secondCentered index member) (distance index)
      (positive index member) (firstSeparated index member) (secondSeparated index member) (small index member)
      weight weightNonnegative (firstRatioSmall index member) (secondRatioSmall index member)
  have sumSummable : Summable (fun power : ℕ =>
      ∑ index ∈ selected, weight ^ (power + 1) * ‖(comparison.source index).coefficientDifference power‖) :=
    summable_sum fun index member => (individual index member).1
  have actual := Summable.of_nonneg_of_le (fun power => by positivity)
    (fun power => comparison.exteriorTaylorCoefficient_weighted_difference_le_sum selected weightNonnegative power)
    sumSummable
  refine ⟨actual, ?_⟩
  have estimate := actual.tsum_le_tsum
    (fun power => comparison.exteriorTaylorCoefficient_weighted_difference_le_sum selected weightNonnegative power) sumSummable
  rw [Summable.tsum_finsetSum (fun index member => (individual index member).1)] at estimate
  exact estimate.trans (Finset.sum_le_sum fun index member => (individual index member).2)

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
