import EulerNonuniqueness.Section3.CanonicalExteriorCommonCoordinateCompatibility

noncomputable section

open Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

local instance commonBoundaryForcingRateC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

open EulerNonuniqueness.Section6 EulerNonuniqueness.General

theorem exists_canonical_common_boundary_forcing_rate :
    ∃ caps : CanonicalCommonBoundaryRateCaps, ∃ constant ≥ 1,
      ∀ {firstCount finalCount : ℕ} (firstFamily : FiniteMovingPatchFamily firstCount)
        (finalFamily : FiniteMovingPatchFamily finalCount) (firstIndex : Fin firstCount) (finalIndex : Fin finalCount)
        (frequency time firstDistance finalDistance weight mass radius : ℝ) (first final : PeriodicC1HolderHalf)
        (comparison : CanonicalCommonBoundaryPairAt caps firstFamily finalFamily firstIndex finalIndex
          frequency time firstDistance finalDistance weight mass radius first final),
      ‖firstFamily.canonicalExteriorCommonQuadraticMaterialForcing firstIndex frequency time (diskPhysicalSpectralChart final)
          comparison.finalResidual comparison.sourceDifference -
        firstFamily.canonicalExteriorCommonQuadraticMaterialForcing firstIndex frequency time (diskPhysicalSpectralChart first)
          comparison.firstResidual 0‖ +
      radius * ‖firstFamily.canonicalExteriorCommonTrueAngularForcing firstIndex frequency time (diskPhysicalSpectralChart final)
          comparison.finalResidual comparison.sourceDifference -
        firstFamily.canonicalExteriorCommonTrueAngularForcing firstIndex frequency time (diskPhysicalSpectralChart first)
          comparison.firstResidual 0‖ ≤
      constant * (|frequency| * radius ^ 2 * comparison.boundaryDistance + comparison.coefficientDifferenceSeries) := by
  obtain ⟨quadraticRaw, quadraticRawPositive, quadraticPhysical, quadraticPhysicalPositive, quadraticForcing, quadraticForcingPositive,
    quadraticShape, quadraticShapePositive, quadraticMaterialConstant, quadraticMaterialOne, quadraticMaterials⟩ :=
    canonicalExteriorCommonQuadraticMaterialResidual_exists_actual_quadratic_rate_ball
  obtain ⟨angularRaw, angularRawPositive, angularPhysical, angularPhysicalPositive, angularForcing, angularForcingPositive,
    angularShape, angularShapePositive, angularMaterialConstant, angularMaterialOne, angularMaterials⟩ :=
    canonicalExteriorCommonTrueAngularMaterialResidual_exists_actual_quadratic_rate_ball
  obtain ⟨sourceRaw, sourceRawPositive, sourcePhysical, sourcePhysicalPositive, sourceSpectral, sourceSpectralPositive,
    sourceField, sourceFieldPositive, sourceConstant, sourceNonnegative, sources⟩ :=
    canonicalProjectedExteriorContourField_exists_common_boundary_source_recipient_ball
  obtain ⟨inverseRaw, inverseRawPositive, inverseForcing, inverseForcingPositive, mapConstant, mapOne,
    inverseNeutral, inverseNeutralPositive, inverseQuadraticConstant, inverseQuadraticOne, rawInverses⟩ :=
    canonicalExteriorCommonRawSpectralCoordinate_exists_quadratic_weighted_inverse_ball
  obtain ⟨selfRadius, selfPositive, selfInverseConstant, selfInverseOne, selfConstant, selfOne, selfs⟩ :=
    diskSpectralQuadraticTrueAngularSelf_exists_weighted_quadratic_rate_ball
  obtain ⟨chartInverseRadius, chartInversePositive, chartInverses⟩ := Metric.eventually_nhds_iff.mp
    diskPhysicalSpectralCoordinate_eventually_left_inverse
  let caps : CanonicalCommonBoundaryRateCaps := {
    rawRadius := min quadraticRaw (min angularRaw (min sourceRaw (min inverseRaw chartInverseRadius)))
    rawPositive := by positivity
    physicalRadius := min quadraticPhysical (min angularPhysical sourcePhysical)
    physicalPositive := by positivity
    spectralRadius := min sourceSpectral (min (selfRadius / 2) (inverseNeutral / (1 + ‖diskRelabelNeutralCLM‖)))
    spectralPositive := by positivity
    fieldRadius := sourceField
    fieldPositive := sourceFieldPositive
    forcingRadius := min quadraticForcing (min angularForcing inverseForcing)
    forcingPositive := by positivity
    shapeRadius := min quadraticShape (min angularShape 1)
    shapePositive := by positivity
    mapConstant := mapConstant
    mapOne := mapOne
    quadraticConstant := max inverseQuadraticConstant selfInverseConstant
    quadraticOne := inverseQuadraticOne.trans (le_max_left _ _) }
  let constant := selfConstant + 4 * (quadraticMaterialConstant + angularMaterialConstant) + sourceConstant + 1
  have quadraticMaterialNonnegative : 0 ≤ quadraticMaterialConstant := by linarith
  have angularMaterialNonnegative : 0 ≤ angularMaterialConstant := by linarith
  have selfNonnegative : 0 ≤ selfConstant := by linarith
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  refine ⟨caps, constant, constantOne, ?_⟩
  intro firstCount finalCount firstFamily finalFamily firstIndex finalIndex frequency time firstDistance finalDistance weight mass radius first final comparison
  have radiusNonnegative := comparison.radiusNonnegative
  have weightNonnegative := comparison.weightNonnegative
  have radiusOne : radius ≤ 1 := comparison.radiusSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have firstInverse : diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart first) = first := by
    apply chartInverses
    simpa only [mem_ball, dist_zero_right] using (ball_subset_ball
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) comparison.firstInside :
        first ∈ ball 0 chartInverseRadius)
  have finalInverse : diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart final) = final := by
    apply chartInverses
    simpa only [mem_ball, dist_zero_right] using (ball_subset_ball
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) comparison.finalInside :
        final ∈ ball 0 chartInverseRadius)
  let firstCorrected := firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart first)
  let finalCorrected := firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart final)
  have firstCorrectedIdentity : firstFamily.canonicalExteriorCommonRawSpectralCoordinate firstIndex frequency time first = firstCorrected := by
    exact firstFamily.canonicalExteriorCommonRawSpectralCoordinate_eq_normalized_physical_of_inverse firstIndex frequency time first firstInverse
  have finalCorrectedIdentity : firstFamily.canonicalExteriorCommonRawSpectralCoordinate firstIndex frequency time final = finalCorrected := by
    exact firstFamily.canonicalExteriorCommonRawSpectralCoordinate_eq_normalized_physical_of_inverse firstIndex frequency time final finalInverse
  have firstSelf : firstCorrected ∈ ball 0 selfRadius := by
    with_reducible_and_instances
      simpa only [mem_ball, dist_zero_right, firstCorrected] using
        (comparison.firstSpectral.trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (half_lt_self selfPositive)
  have finalSelf : finalCorrected ∈ ball 0 selfRadius := by
    with_reducible_and_instances
      simpa only [mem_ball, dist_zero_right, finalCorrected] using
        (comparison.finalSpectral.trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (half_lt_self selfPositive)
  have selfSmall : selfInverseConstant * radius ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (le_max_right inverseQuadraticConstant selfInverseConstant) comparison.radiusNonnegative).trans comparison.quadraticSmall
  have selfBound := by
    with_reducible_and_instances
      exact selfs firstCorrected finalCorrected firstSelf finalSelf comparison.firstCorrectedArea comparison.finalCorrectedArea
        comparison.radiusNonnegative comparison.firstCorrectedTransverse comparison.finalCorrectedTransverse selfSmall (frequency := frequency)
  have neutralBound {state : PeriodicC1HolderHalf} (bound : ‖state‖ ≤ caps.spectralRadius) : ‖diskRelabelNeutralCLM state‖ ≤ inverseNeutral := by
    with_reducible_and_instances
      have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskRelabelNeutralCLM‖)).mp
        (bound.trans ((min_le_right _ _).trans (min_le_right _ _)))
      calc
        ‖diskRelabelNeutralCLM state‖ ≤ ‖diskRelabelNeutralCLM‖ * ‖state‖ := diskRelabelNeutralCLM.le_opNorm state
        _ ≤ (1 + ‖diskRelabelNeutralCLM‖) * ‖state‖ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg state)
        _ = ‖state‖ * (1 + ‖diskRelabelNeutralCLM‖) := mul_comm _ _
        _ ≤ inverseNeutral := scaled
  have firstRawInverse : first ∈ ball 0 inverseRaw :=
    ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) comparison.firstInside
  have finalRawInverse : final ∈ ball 0 inverseRaw :=
    ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) comparison.finalInside
  have scale48 : 48 * (firstFamily.patch firstIndex).radius ≤ firstDistance := by
    linarith [comparison.firstScale, (firstFamily.patch firstIndex).radius_positive]
  have rawBound := by
    with_reducible_and_instances
      exact rawInverses firstFamily firstIndex first final firstRawInverse finalRawInverse
        comparison.firstArea comparison.finalArea comparison.firstCentered comparison.finalCentered comparison.frequencyNonzero
        comparison.firstPositive comparison.weightNonnegative scale48 comparison.firstSeparated comparison.weightBound
        (comparison.forcingSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) comparison.radiusNonnegative radiusOne comparison.mapSmall
  have rawInverse := by
    with_reducible_and_instances
      dsimp only at rawBound
      rw [firstCorrectedIdentity, finalCorrectedIdentity] at rawBound
      exact rawBound (neutralBound comparison.firstSpectral) (neutralBound comparison.finalSpectral)
        comparison.firstCorrectedTransverse comparison.finalCorrectedTransverse
        ((mul_le_mul_of_nonneg_right (le_max_left inverseQuadraticConstant selfInverseConstant) comparison.radiusNonnegative).trans comparison.quadraticSmall)
  have quadraticMaterial := quadraticMaterials firstFamily firstIndex first final
    (ball_subset_ball (min_le_left _ _) comparison.firstInside) (ball_subset_ball (min_le_left _ _) comparison.finalInside)
    comparison.firstMember comparison.finalMember comparison.firstPhysicalMember comparison.finalPhysicalMember
    comparison.firstArea comparison.finalArea comparison.firstCentered comparison.finalCentered comparison.firstSmall comparison.finalSmall
    comparison.frequencyNonzero comparison.timeInside comparison.material comparison.centerIdentity comparison.firstPositive comparison.weightNonnegative
    comparison.massNonnegative comparison.radiusNonnegative (comparison.radiusSmall.trans (min_le_left _ _))
    comparison.firstTransverse comparison.finalTransverse comparison.firstScale comparison.firstSeparated comparison.weightBound comparison.massBound
    (comparison.forcingSmall.trans (min_le_left _ _)) comparison.epsilonSmall comparison.squaredSmall comparison.tailSmall comparison.derivativeScale
    (comparison.firstPhysical.trans (min_le_left _ _)) (comparison.finalPhysical.trans (min_le_left _ _))
  have angularMaterial := angularMaterials firstFamily firstIndex first final
    (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) comparison.firstInside)
    (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) comparison.finalInside)
    comparison.firstMember comparison.finalMember comparison.firstPhysicalMember comparison.finalPhysicalMember
    comparison.firstArea comparison.finalArea comparison.firstCentered comparison.finalCentered comparison.firstSmall comparison.finalSmall
    comparison.frequencyNonzero comparison.timeInside comparison.material comparison.centerIdentity comparison.firstPositive comparison.weightNonnegative
    comparison.massNonnegative comparison.radiusNonnegative (comparison.radiusSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
    comparison.firstTransverse comparison.finalTransverse comparison.firstScale comparison.firstSeparated comparison.weightBound comparison.massBound
    (comparison.forcingSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) comparison.epsilonSmall comparison.squaredSmall comparison.tailSmall comparison.derivativeScale
    (comparison.firstPhysical.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (comparison.finalPhysical.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have source := sources firstFamily finalFamily firstIndex finalIndex final
    (ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) comparison.finalInside)
    comparison.frequencyNonzero comparison.firstPositive comparison.finalPositive comparison.weightNonnegative comparison.radiusNonnegative radiusOne
    comparison.firstScale comparison.finalScale comparison.firstSeparated comparison.finalSeparated comparison.weightBound
    (comparison.epsilonSmall.trans radiusOne)
    (comparison.finalPhysical.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (comparison.finalSpectral.trans (min_le_left _ _)) comparison.finalField
  with_reducible_and_instances dsimp only at source
  have opposite :
      firstFamily.canonicalProjectedExteriorContourField firstIndex time firstDistance comparison.firstPositive
          (by linarith [comparison.firstScale, (firstFamily.patch firstIndex).radius_positive]) comparison.firstSeparated
          (Circle.exp (frequency * time / 2)) (diskPhysicalSpectralChart final) -
        finalFamily.canonicalProjectedExteriorContourField finalIndex time finalDistance comparison.finalPositive
          (by linarith [comparison.finalScale, (finalFamily.patch finalIndex).radius_positive]) comparison.finalSeparated
          (Circle.exp (frequency * time / 2)) (diskPhysicalSpectralChart final) = -comparison.sourceDifference := by
    with_reducible_and_instances
      unfold CanonicalCommonBoundaryPairAt.sourceDifference
      abel
  with_reducible_and_instances
    rw [opposite, map_neg, norm_neg, map_neg, norm_neg] at source
  let firstQuadraticMaterial := firstFamily.canonicalExteriorCommonQuadraticMaterialResidual firstIndex frequency time firstDistance
    comparison.firstPositive (by linarith [comparison.firstScale, (firstFamily.patch firstIndex).radius_positive]) comparison.firstSeparated
    (diskPhysicalSpectralChart first) comparison.firstSmall
  let finalQuadraticMaterial := firstFamily.canonicalExteriorCommonQuadraticMaterialResidual firstIndex frequency time firstDistance
    comparison.firstPositive (by linarith [comparison.firstScale, (firstFamily.patch firstIndex).radius_positive]) comparison.firstSeparated
    (diskPhysicalSpectralChart final) comparison.finalSmall
  let firstAngularMaterial := firstFamily.canonicalExteriorCommonTrueAngularMaterialResidual firstIndex frequency time firstDistance
    comparison.firstPositive (by linarith [comparison.firstScale, (firstFamily.patch firstIndex).radius_positive]) comparison.firstSeparated
    (diskPhysicalSpectralChart first) comparison.firstSmall
  let finalAngularMaterial := firstFamily.canonicalExteriorCommonTrueAngularMaterialResidual firstIndex frequency time firstDistance
    comparison.firstPositive (by linarith [comparison.firstScale, (firstFamily.patch firstIndex).radius_positive]) comparison.firstSeparated
    (diskPhysicalSpectralChart final) comparison.finalSmall
  let rawDistance := ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
    radius * ‖diskNeutralCLM first - diskNeutralCLM final‖
  have rawDistanceNonnegative : 0 ≤ rawDistance := by dsimp only [rawDistance]; positivity
  have distanceNonnegative : 0 ≤ comparison.boundaryDistance := by
    unfold CanonicalCommonBoundaryPairAt.boundaryDistance weightedBoundaryPairDistance
    positivity
  have coefficientNonnegative : 0 ≤ comparison.coefficientDifferenceSeries :=
    tsum_nonneg (fun degree => mul_nonneg (by positivity) (norm_nonneg _))
  have materialBound : ‖finalQuadraticMaterial - firstQuadraticMaterial‖ + radius * ‖finalAngularMaterial - firstAngularMaterial‖ ≤
      (quadraticMaterialConstant + angularMaterialConstant) * |frequency| * radius ^ 2 * rawDistance := by
    rw [norm_sub_rev, norm_sub_rev finalAngularMaterial firstAngularMaterial]
    have angularScaled := (mul_le_mul_of_nonneg_left angularMaterial comparison.radiusNonnegative).trans
      (mul_le_of_le_one_left (by positivity : 0 ≤ angularMaterialConstant * |frequency| * radius ^ 2 * rawDistance) radiusOne)
    exact (add_le_add quadraticMaterial angularScaled).trans_eq (by ring)
  have rawInverseActual : rawDistance ≤ 4 * comparison.boundaryDistance := by
    with_reducible_and_instances
      simpa only [rawDistance, weightedProjectionDistance, map_sub, CanonicalCommonBoundaryPairAt.boundaryDistance,
        weightedBoundaryPairDistance, canonicalExteriorCommonQuadraticCoordinate, canonicalExteriorCommonTrueAngularCoordinate,
        firstCorrected, finalCorrected, norm_sub_rev] using rawInverse
  have materialCorrected := materialBound.trans (mul_le_mul_of_nonneg_left rawInverseActual
    (by positivity : 0 ≤ (quadraticMaterialConstant + angularMaterialConstant) * |frequency| * radius ^ 2))
  have selfActual :
      ‖frequency • diskSpectralMovingSelfRemainder finalCorrected - frequency • diskSpectralMovingSelfRemainder firstCorrected‖ +
        radius * ‖frequency • diskNeutralCLM (diskSpectralTubularEulerField finalCorrected) -
          frequency • diskNeutralCLM (diskSpectralTubularEulerField firstCorrected)‖ ≤
      selfConstant * |frequency| * radius ^ 2 * comparison.boundaryDistance := by
    with_reducible_and_instances
      simpa only [CanonicalCommonBoundaryPairAt.boundaryDistance, weightedBoundaryPairDistance,
        canonicalExteriorCommonQuadraticCoordinate, canonicalExteriorCommonTrueAngularCoordinate, firstCorrected, finalCorrected,
        norm_sub_rev] using selfBound
  have split (firstSelf finalSelf firstMaterial finalMaterial sourceTerm firstNeutralSelf finalNeutralSelf firstNeutralMaterial finalNeutralMaterial neutralSource : PeriodicC1HolderHalf) :
      ‖(finalSelf + finalMaterial + sourceTerm) - (firstSelf + firstMaterial)‖ +
        radius * ‖(finalNeutralSelf + finalNeutralMaterial + neutralSource) - (firstNeutralSelf + firstNeutralMaterial)‖ ≤
      (‖finalSelf - firstSelf‖ + radius * ‖finalNeutralSelf - firstNeutralSelf‖) +
        (‖finalMaterial - firstMaterial‖ + radius * ‖finalNeutralMaterial - firstNeutralMaterial‖) +
        (‖sourceTerm‖ + radius * ‖neutralSource‖) := by
    have triple (firstSelf finalSelf firstMaterial finalMaterial sourceTerm : PeriodicC1HolderHalf) :
        ‖(finalSelf + finalMaterial + sourceTerm) - (firstSelf + firstMaterial)‖ ≤
          ‖finalSelf - firstSelf‖ + ‖finalMaterial - firstMaterial‖ + ‖sourceTerm‖ := by
      have identity : (finalSelf + finalMaterial + sourceTerm) - (firstSelf + firstMaterial) =
          (finalSelf - firstSelf) + (finalMaterial - firstMaterial) + sourceTerm := by abel
      rw [identity]
      exact (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    have actual := add_le_add (triple firstSelf finalSelf firstMaterial finalMaterial sourceTerm)
      (mul_le_mul_of_nonneg_left (triple firstNeutralSelf finalNeutralSelf firstNeutralMaterial finalNeutralMaterial neutralSource) comparison.radiusNonnegative)
    nlinarith only [actual]
  have triangle := split
    (frequency • diskSpectralMovingSelfRemainder firstCorrected) (frequency • diskSpectralMovingSelfRemainder finalCorrected)
    firstQuadraticMaterial finalQuadraticMaterial
    (firstFamily.canonicalExteriorCommonQuadraticSourceOperator firstIndex frequency time (diskPhysicalSpectralChart final) comparison.sourceDifference)
    (frequency • diskNeutralCLM (diskSpectralTubularEulerField firstCorrected))
    (frequency • diskNeutralCLM (diskSpectralTubularEulerField finalCorrected)) firstAngularMaterial finalAngularMaterial
    (firstFamily.canonicalExteriorCommonTrueAngularSourceOperator firstIndex frequency time (diskPhysicalSpectralChart final) comparison.sourceDifference)
  have bounded := triangle.trans (add_le_add (add_le_add selfActual materialCorrected) source)
  have stateCoefficient : selfConstant + 4 * (quadraticMaterialConstant + angularMaterialConstant) ≤ constant := by dsimp only [constant]; linarith
  have sourceCoefficient : sourceConstant ≤ constant := by dsimp only [constant]; linarith
  have scalar := add_le_add (mul_le_mul_of_nonneg_right stateCoefficient
    (by positivity : 0 ≤ |frequency| * radius ^ 2 * comparison.boundaryDistance))
      (mul_le_mul_of_nonneg_right sourceCoefficient coefficientNonnegative)
  have result :
      ‖(frequency • diskSpectralMovingSelfRemainder finalCorrected + finalQuadraticMaterial +
          firstFamily.canonicalExteriorCommonQuadraticSourceOperator firstIndex frequency time (diskPhysicalSpectralChart final) comparison.sourceDifference) -
        (frequency • diskSpectralMovingSelfRemainder firstCorrected + firstQuadraticMaterial)‖ +
      radius * ‖(frequency • diskNeutralCLM (diskSpectralTubularEulerField finalCorrected) + finalAngularMaterial +
          firstFamily.canonicalExteriorCommonTrueAngularSourceOperator firstIndex frequency time (diskPhysicalSpectralChart final) comparison.sourceDifference) -
        (frequency • diskNeutralCLM (diskSpectralTubularEulerField firstCorrected) + firstAngularMaterial)‖ ≤
      constant * (|frequency| * radius ^ 2 * comparison.boundaryDistance + comparison.coefficientDifferenceSeries) := by
    apply bounded.trans
    convert scalar using 1 <;> simp only [CanonicalCommonBoundaryPairAt.coefficientDifferenceSeries] <;> ring
  with_reducible_and_instances
    simpa only [canonicalExteriorCommonQuadraticMaterialForcing, canonicalExteriorCommonTrueAngularForcing,
      CanonicalCommonBoundaryPairAt.firstResidual, CanonicalCommonBoundaryPairAt.finalResidual,
      firstCorrected, finalCorrected, firstQuadraticMaterial, finalQuadraticMaterial, firstAngularMaterial, finalAngularMaterial,
      canonicalExteriorCommonQuadraticMaterialResidual, canonicalExteriorCommonTrueAngularMaterialResidual,
      diskNormalizedQuadraticError, diskNormalizedTrueAngularError, canonicalExteriorCommonNormalizedPhysicalCoordinate,
      canonicalExteriorCommonTrueAngularSourceOperator, ContinuousLinearMap.comp_apply, map_zero, add_zero] using result

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
