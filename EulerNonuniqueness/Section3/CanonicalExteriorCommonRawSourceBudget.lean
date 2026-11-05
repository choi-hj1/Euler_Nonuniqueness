import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryHistory
import EulerNonuniqueness.Section3.CanonicalExteriorCommonCoordinateCompatibility

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

local instance commonRawSourceBudgetC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

open EulerNonuniqueness.General EulerNonuniqueness.Section6

theorem exists_canonical_common_boundary_raw_source_budget :
    ∃ caps : CanonicalCommonBoundaryRateCaps, ∃ constant ≥ (1 : ℝ),
    ∀ {firstCount finalCount : ℕ} (firstFamily : FiniteMovingPatchFamily firstCount)
      (finalFamily : FiniteMovingPatchFamily finalCount) (firstIndex : Fin firstCount) (finalIndex : Fin finalCount)
      (frequency time firstDistance finalDistance weight mass radius : ℝ) (first final : PeriodicC1HolderHalf),
    ∀ comparison : CanonicalCommonBoundaryPairAt caps firstFamily finalFamily firstIndex finalIndex
      frequency time firstDistance finalDistance weight mass radius first final,
    ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
      (‖diskPhysicalTransverseProjection first‖ + ‖diskPhysicalTransverseProjection final‖) *
        ‖diskNeutralCLM first - diskNeutralCLM final‖ ≤ constant * comparison.boundaryDistance := by
  obtain ⟨inverseRadius, inversePositive, forcingRadius, forcingPositive, mapConstant, mapOne,
    neutralRadius, neutralPositive, quadraticConstant, quadraticOne, inverses⟩ :=
    canonicalExteriorCommonRawSpectralCoordinate_exists_quadratic_weighted_inverse_ball
  obtain ⟨chartRadius, chartPositive, chartInverses⟩ := Metric.eventually_nhds_iff.mp
    diskPhysicalSpectralCoordinate_eventually_left_inverse
  let caps : CanonicalCommonBoundaryRateCaps := {
    rawRadius := min inverseRadius chartRadius
    rawPositive := lt_min inversePositive chartPositive
    physicalRadius := 1
    physicalPositive := zero_lt_one
    spectralRadius := neutralRadius / (1 + ‖diskRelabelNeutralCLM‖)
    spectralPositive := by positivity
    fieldRadius := 1
    fieldPositive := zero_lt_one
    forcingRadius := forcingRadius
    forcingPositive := forcingPositive
    shapeRadius := 1
    shapePositive := zero_lt_one
    mapConstant := mapConstant
    mapOne := mapOne
    quadraticConstant := quadraticConstant
    quadraticOne := quadraticOne }
  let constant := (8 : ℝ)
  refine ⟨caps, constant, by norm_num [constant], ?_⟩
  intro firstCount finalCount firstFamily finalFamily firstIndex finalIndex frequency time firstDistance finalDistance weight mass radius first final comparison
  have firstInverse : diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart first) = first := by
    apply chartInverses
    simpa only [mem_ball, dist_zero_right] using
      (ball_subset_ball (min_le_right inverseRadius chartRadius) comparison.firstInside : first ∈ ball 0 chartRadius)
  have finalInverse : diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart final) = final := by
    apply chartInverses
    simpa only [mem_ball, dist_zero_right] using
      (ball_subset_ball (min_le_right inverseRadius chartRadius) comparison.finalInside : final ∈ ball 0 chartRadius)
  have firstCorrected := firstFamily.canonicalExteriorCommonRawSpectralCoordinate_eq_normalized_physical_of_inverse
    firstIndex frequency time first firstInverse
  have finalCorrected := firstFamily.canonicalExteriorCommonRawSpectralCoordinate_eq_normalized_physical_of_inverse
    firstIndex frequency time final finalInverse
  have neutralBound {state : PeriodicC1HolderHalf} (bounded : ‖state‖ ≤ caps.spectralRadius) :
      ‖diskRelabelNeutralCLM state‖ ≤ neutralRadius := by
    have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskRelabelNeutralCLM‖)).mp bounded
    calc
      ‖diskRelabelNeutralCLM state‖ ≤ ‖diskRelabelNeutralCLM‖ * ‖state‖ := diskRelabelNeutralCLM.le_opNorm state
      _ ≤ (1 + ‖diskRelabelNeutralCLM‖) * ‖state‖ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_lt_one.le) (norm_nonneg _)
      _ = ‖state‖ * (1 + ‖diskRelabelNeutralCLM‖) := mul_comm _ _
      _ ≤ neutralRadius := scaled
  have small : 48 * (firstFamily.patch firstIndex).radius ≤ firstDistance := by
    linarith [comparison.firstScale, (firstFamily.patch firstIndex).radius_positive]
  have firstInside : first ∈ ball 0 inverseRadius := ball_subset_ball (min_le_left _ _) comparison.firstInside
  have finalInside : final ∈ ball 0 inverseRadius := ball_subset_ball (min_le_left _ _) comparison.finalInside
  have raw := by
    with_reducible_and_instances
      exact inverses firstFamily firstIndex first final firstInside finalInside comparison.firstArea comparison.finalArea
        comparison.firstCentered comparison.finalCentered comparison.frequencyNonzero comparison.firstPositive comparison.weightNonnegative
        small comparison.firstSeparated comparison.weightBound comparison.forcingSmall comparison.radiusNonnegative comparison.radiusSmall comparison.mapSmall
  have rawBound := by
    with_reducible_and_instances
      dsimp only at raw
      rw [firstCorrected, finalCorrected] at raw
      exact raw (neutralBound comparison.firstSpectral) (neutralBound comparison.finalSpectral)
        comparison.firstCorrectedTransverse comparison.finalCorrectedTransverse comparison.quadraticSmall
  have transverseSum : ‖diskPhysicalTransverseProjection first‖ + ‖diskPhysicalTransverseProjection final‖ ≤ 2 * radius :=
    (add_le_add comparison.firstTransverse comparison.finalTransverse).trans_eq (by ring)
  have budgetBound : ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
      (‖diskPhysicalTransverseProjection first‖ + ‖diskPhysicalTransverseProjection final‖) *
        ‖diskNeutralCLM first - diskNeutralCLM final‖ ≤
      2 *
        (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
          radius * ‖diskNeutralCLM first - diskNeutralCLM final‖) := by
    have scaled := mul_le_mul_of_nonneg_right transverseSum (norm_nonneg (diskNeutralCLM first - diskNeutralCLM final))
    nlinarith only [scaled, norm_nonneg (diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final)]
  have distanceBound : ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
      radius * ‖diskNeutralCLM first - diskNeutralCLM final‖ ≤ 4 * comparison.boundaryDistance := by
    with_reducible_and_instances
      simpa only [weightedProjectionDistance, map_sub, CanonicalCommonBoundaryPairAt.boundaryDistance,
        canonicalExteriorCommonQuadraticCoordinate, canonicalExteriorCommonTrueAngularCoordinate, weightedBoundaryPairDistance, norm_sub_rev]
        using rawBound
  have scaled := mul_le_mul_of_nonneg_left distanceBound (by norm_num : (0 : ℝ) ≤ 2)
  exact budgetBound.trans (scaled.trans_eq (by dsimp only [constant]; ring))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
