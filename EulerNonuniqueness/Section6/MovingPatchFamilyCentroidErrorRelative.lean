import EulerNonuniqueness.Section3.MovingCanonicalCentroidResponseRelative
import EulerNonuniqueness.Section6.MovingPatchVelocityCorrectionRelative
import EulerNonuniqueness.Section6.MovingPatchFamilySourceComparison

noncomputable section

open Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem centroidPointError_exists_relative_bound :
    ∃ radius > (0 : ℝ), ∃ parameterRadius > (0 : ℝ),
      ∃ sourceConstant ≥ (0 : ℝ), ∃ receiverConstant ≥ (0 : ℝ),
      ∀ count : ℕ, ∀ comparison : MovingPatchFamilySourceComparison count,
      ∀ selected : Finset (Fin count), ∀ receiver : Fin count,
      (∀ label, comparison.initial label ∈ ball 0 radius) →
      (∀ label, comparison.final label ∈ ball 0 radius) →
      (∀ label, contourCentroidFunctional ((comparison.first.patch label).shape comparison.time) = 0) →
      (∀ label, contourCentroidFunctional ((comparison.second.patch label).shape comparison.time) = 0) →
      (∀ label ∈ selected, (comparison.first.patch label).center comparison.time =
        (comparison.first.patch label).centroid comparison.time) →
      ∀ distance travel : Fin count → ℝ,
      (∀ label ∈ selected, 0 < distance label) → (∀ label ∈ selected, 0 ≤ travel label) →
      (∀ label ∈ selected, 2 * (comparison.first.patch label).radius + travel label + distance label ≤
        ‖comparison.firstReceiver comparison.time - (comparison.first.patch label).center comparison.time‖) →
      (∀ label ∈ selected, 2 * (comparison.first.patch label).radius + distance label ≤
        ‖comparison.secondReceiver comparison.time - (comparison.second.patch label).center comparison.time‖) →
      (∀ label ∈ selected, ‖(comparison.source label).displacementDifference‖ ≤ travel label) →
      (∀ label ∈ selected, (comparison.first.patch label).radius /
        ‖comparison.secondReceiver comparison.time - (comparison.second.patch label).center comparison.time‖ ≤ parameterRadius) →
      ∀ virtualRadius : ℝ, 0 < comparison.receiverRadius → 0 < virtualRadius →
      comparison.receiverRadius ≤ virtualRadius → ∀ phase : Circle,
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver virtualRadius (power + 1) comparison.time‖) →
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖comparison.second.exteriorTaylorCoefficient selected comparison.secondReceiver virtualRadius (power + 1) comparison.time‖) →
      ‖(∑ label ∈ selected, (comparison.source label).velocityCentroidCorrectionDifference) +
        (comparison.receiverRadius • ((phase : ℂ) *
          contourExteriorCentroidResponse phase
            (fun power => comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver
              comparison.receiverRadius (power + 1) comparison.time)
            (diskPhysicalSpectralChart (comparison.initial receiver))) -
        comparison.receiverRadius • ((phase : ℂ) *
          contourExteriorCentroidResponse phase
            (fun power => comparison.second.exteriorTaylorCoefficient selected comparison.secondReceiver
              comparison.receiverRadius (power + 1) comparison.time)
            (diskPhysicalSpectralChart (comparison.final receiver))))‖ ≤
      (∑ label ∈ selected,
        ((comparison.source label).velocityCentroidCorrectionCenterEnvelope (distance label) +
          (comparison.source label).velocityCentroidCorrectionShapeEnvelope sourceConstant)) +
      receiverConstant * (comparison.receiverRadius ^ 2 / virtualRadius) *
        ((∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
          ‖comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver virtualRadius (power + 1) comparison.time‖) *
          (comparison.source receiver).spectralDifferenceBudget +
        (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
          ‖comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver virtualRadius (power + 1) comparison.time -
            comparison.second.exteriorTaylorCoefficient selected comparison.secondReceiver virtualRadius (power + 1) comparison.time‖) *
          ‖diskPhysicalTransverseProjection (comparison.final receiver)‖) := by
  obtain ⟨sourceRadius, sourcePositive, parameterRadius, parameterPositive, sourceConstant, sourceNonnegative, sourceBound⟩ :=
    MovingPatchSourceComparison.velocityCentroidCorrection_exists_centered_relative_bound
  obtain ⟨receiverRadius, receiverPositive, receiverConstant, receiverNonnegative, receiverBound⟩ :=
    exists_uniform_material_centroid_response_relative
  refine ⟨min sourceRadius receiverRadius, by positivity, parameterRadius, parameterPositive,
    sourceConstant, sourceNonnegative, receiverConstant, receiverNonnegative, ?_⟩
  intro count comparison selected receiver initialInside finalInside firstCentered secondCentered trueCenter
    distance travel positive travelNonnegative firstSeparated secondSeparated travelBound small virtualRadius
    physicalPositive virtualPositive physicalSmall phase firstSummable secondSummable
  have corrections (label : Fin count) (member : label ∈ selected) := sourceBound (comparison.source label)
    (ball_subset_ball (min_le_left _ _) (initialInside label))
    (ball_subset_ball (min_le_left _ _) (finalInside label))
    (firstCentered label) (secondCentered label) (trueCenter label member)
    (distance label) (travel label) (positive label member) (travelNonnegative label member)
    (firstSeparated label member) (secondSeparated label member) (travelBound label member) (small label member)
  have initialArea : diskSpectralTubularArea (comparison.initial receiver) = Real.pi := by
    change contourAreaFunctional (diskPhysicalSpectralChart (comparison.initial receiver)) = Real.pi
    rw [← comparison.firstShape receiver]
    exact (comparison.first.patch receiver).normalized_shape_area_eq_pi_of_domain_area comparison.time
      (comparison.firstArea receiver)
  have finalArea : diskSpectralTubularArea (comparison.final receiver) = Real.pi := by
    change contourAreaFunctional (diskPhysicalSpectralChart (comparison.final receiver)) = Real.pi
    rw [← comparison.secondShape receiver]
    exact (comparison.second.patch receiver).normalized_shape_area_eq_pi_of_domain_area comparison.time
      (comparison.secondArea receiver)
  have response := receiverBound count comparison.first comparison.second selected comparison.firstReceiver
    comparison.secondReceiver comparison.receiverRadius virtualRadius comparison.time physicalPositive virtualPositive physicalSmall
    (comparison.initial receiver) (comparison.final receiver)
    (ball_subset_ball (min_le_right _ _) (initialInside receiver))
    (ball_subset_ball (min_le_right _ _) (finalInside receiver)) initialArea finalArea
    (by simpa only [comparison.firstShape receiver] using firstCentered receiver)
    (by simpa only [comparison.secondShape receiver] using secondCentered receiver)
    phase firstSummable secondSummable
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun label member => corrections label member)) response)

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
