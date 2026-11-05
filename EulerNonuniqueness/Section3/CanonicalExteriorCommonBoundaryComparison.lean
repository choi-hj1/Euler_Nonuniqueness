import EulerNonuniqueness.Section3.CanonicalExteriorCommonQuadraticMaterialRate
import EulerNonuniqueness.Section3.CanonicalExteriorCommonTrueAngularMaterialRate
import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundarySourceRecipient
import EulerNonuniqueness.Section3.CanonicalExteriorCommonQuadraticRawInverse
import EulerNonuniqueness.Section3.CanonicalExteriorCommonQuadraticHistory
import EulerNonuniqueness.Section3.CanonicalExteriorCommonTrueAngularHistory
import EulerNonuniqueness.Section3.DiskQuadraticTrueAngularSelfRate
import EulerNonuniqueness.General.QuadraticNeutralPairHistory

noncomputable section

open Filter Metric MeasureTheory Set
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

structure CanonicalCommonBoundaryRateCaps where
  rawRadius : ℝ
  rawPositive : 0 < rawRadius
  physicalRadius : ℝ
  physicalPositive : 0 < physicalRadius
  spectralRadius : ℝ
  spectralPositive : 0 < spectralRadius
  fieldRadius : ℝ
  fieldPositive : 0 < fieldRadius
  forcingRadius : ℝ
  forcingPositive : 0 < forcingRadius
  shapeRadius : ℝ
  shapePositive : 0 < shapeRadius
  mapConstant : ℝ
  mapOne : 1 ≤ mapConstant
  quadraticConstant : ℝ
  quadraticOne : 1 ≤ quadraticConstant

structure CanonicalCommonBoundaryPairAt
    (caps : CanonicalCommonBoundaryRateCaps) {firstCount finalCount : ℕ}
    (firstFamily : FiniteMovingPatchFamily firstCount) (finalFamily : FiniteMovingPatchFamily finalCount)
    (firstIndex : Fin firstCount) (finalIndex : Fin finalCount)
    (frequency time firstDistance finalDistance weight mass radius : ℝ)
    (first final : PeriodicC1HolderHalf) : Prop where
  firstInside : first ∈ ball 0 caps.rawRadius
  finalInside : final ∈ ball 0 caps.rawRadius
  firstMember : first ∈ contourContinuousVectorSubmodule
  finalMember : final ∈ contourContinuousVectorSubmodule
  firstPhysicalMember : diskPhysicalSpectralChart first ∈ contourContinuousVectorSubmodule
  finalPhysicalMember : diskPhysicalSpectralChart final ∈ contourContinuousVectorSubmodule
  firstArea : diskSpectralTubularArea first = Real.pi
  finalArea : diskSpectralTubularArea final = Real.pi
  firstCentered : contourCentroidFunctional (diskPhysicalSpectralChart first) = 0
  finalCentered : contourCentroidFunctional (diskPhysicalSpectralChart final) = 0
  firstSmall : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart first))‖ < 1 / 2
  finalSmall : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart final))‖ < 1 / 2
  frequencyNonzero : frequency ≠ 0
  timeInside : time ∈ Ioo (firstFamily.patch firstIndex).initialTime (firstFamily.patch firstIndex).finalTime
  material : ∀ label, (firstFamily.patch firstIndex).boundaryVelocity time label =
    biotSavart (firstFamily.vorticity time) ((firstFamily.patch firstIndex).boundary time label)
  centerIdentity : (firstFamily.patch firstIndex).center =ᶠ[nhds time] (firstFamily.patch firstIndex).centroid
  firstPositive : 0 < firstDistance
  finalPositive : 0 < finalDistance
  weightNonnegative : 0 ≤ weight
  massNonnegative : 0 ≤ mass
  radiusNonnegative : 0 ≤ radius
  radiusSmall : radius ≤ caps.shapeRadius
  firstTransverse : ‖diskPhysicalTransverseProjection first‖ ≤ radius
  finalTransverse : ‖diskPhysicalTransverseProjection final‖ ≤ radius
  firstScale : 192 * (firstFamily.patch firstIndex).radius ≤ firstDistance
  finalScale : 192 * (finalFamily.patch finalIndex).radius ≤ finalDistance
  firstSeparated : ∀ source ∈ Finset.univ.erase firstIndex, ∀ position ∈ (firstFamily.patch source).domain time,
    firstDistance ≤ ‖(firstFamily.patch firstIndex).center time - position‖
  finalSeparated : ∀ source ∈ Finset.univ.erase finalIndex, ∀ position ∈ (finalFamily.patch source).domain time,
    finalDistance ≤ ‖(finalFamily.patch finalIndex).center time - position‖
  weightBound : (∫ position, inverseSquareVorticityWeight
    (firstFamily.subfamilyVorticity (Finset.univ.erase firstIndex) time) ((firstFamily.patch firstIndex).center time) position) ≤ weight
  massBound : (∫ position, |firstFamily.patchVorticity time firstIndex position|) ≤ mass
  forcingSmall : weight / |frequency| ≤ caps.forcingRadius
  epsilonSmall : weight / |frequency| ≤ radius
  squaredSmall : (weight / |frequency|) ^ 2 ≤ radius ^ 3
  tailSmall : (weight / |frequency|) * ((firstFamily.patch firstIndex).radius / firstDistance) ≤ radius ^ 2
  derivativeScale : (12 * (46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * firstDistance ^ 2))) / |frequency| ≤
    |frequency| * radius ^ 3
  firstPhysical : ‖firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart first) - standardCircleBanach‖ ≤ caps.physicalRadius
  finalPhysical : ‖firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart final) - standardCircleBanach‖ ≤ caps.physicalRadius
  firstSpectral : ‖firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart first)‖ ≤ caps.spectralRadius
  finalSpectral : ‖firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart final)‖ ≤ caps.spectralRadius
  firstCorrectedArea : diskSpectralTubularArea
    (firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart first)) = Real.pi
  finalCorrectedArea : diskSpectralTubularArea
    (firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart final)) = Real.pi
  firstCorrectedTransverse : ‖diskPhysicalTransverseProjection
    (firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart first))‖ ≤ radius
  finalCorrectedTransverse : ‖diskPhysicalTransverseProjection
    (firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart final))‖ ≤ radius
  mapSmall : (‖diskPhysicalTransverseProjection‖ + ‖diskNeutralCLM‖) *
    (caps.mapConstant * (weight / |frequency|)) ≤ radius / 2
  quadraticSmall : caps.quadraticConstant * radius ≤ 1 / 2
  finalField : ‖diskPhysicalSpectralChart final - standardCircleBanach‖ ≤ caps.fieldRadius

namespace CanonicalCommonBoundaryPairAt

variable {caps : CanonicalCommonBoundaryRateCaps} {firstCount finalCount : ℕ}
  {firstFamily : FiniteMovingPatchFamily firstCount} {finalFamily : FiniteMovingPatchFamily finalCount}
  {firstIndex : Fin firstCount} {finalIndex : Fin finalCount}
  {frequency time firstDistance finalDistance weight mass radius : ℝ}
  {first final : PeriodicC1HolderHalf}

def sourceDifference
    (comparison : CanonicalCommonBoundaryPairAt caps firstFamily finalFamily firstIndex finalIndex
      frequency time firstDistance finalDistance weight mass radius first final) : PeriodicC1HolderHalf :=
  finalFamily.canonicalProjectedExteriorContourField finalIndex time finalDistance comparison.finalPositive
    (by linarith [comparison.finalScale, (finalFamily.patch finalIndex).radius_positive]) comparison.finalSeparated
    (Circle.exp (frequency * time / 2)) (diskPhysicalSpectralChart final) -
  firstFamily.canonicalProjectedExteriorContourField firstIndex time firstDistance comparison.firstPositive
    (by linarith [comparison.firstScale, (firstFamily.patch firstIndex).radius_positive]) comparison.firstSeparated
    (Circle.exp (frequency * time / 2)) (diskPhysicalSpectralChart final)

def firstResidual
    (comparison : CanonicalCommonBoundaryPairAt caps firstFamily finalFamily firstIndex finalIndex
      frequency time firstDistance finalDistance weight mass radius first final) : PeriodicC1HolderHalf :=
  firstFamily.canonicalExteriorCommonMaterialResidual firstIndex frequency time firstDistance comparison.firstPositive
    (by linarith [comparison.firstScale, (firstFamily.patch firstIndex).radius_positive]) comparison.firstSeparated
    (diskPhysicalSpectralChart first) comparison.firstSmall

def finalResidual
    (comparison : CanonicalCommonBoundaryPairAt caps firstFamily finalFamily firstIndex finalIndex
      frequency time firstDistance finalDistance weight mass radius first final) : PeriodicC1HolderHalf :=
  firstFamily.canonicalExteriorCommonMaterialResidual firstIndex frequency time firstDistance comparison.firstPositive
    (by linarith [comparison.firstScale, (firstFamily.patch firstIndex).radius_positive]) comparison.firstSeparated
    (diskPhysicalSpectralChart final) comparison.finalSmall

def boundaryDistance
    (_comparison : CanonicalCommonBoundaryPairAt caps firstFamily finalFamily firstIndex finalIndex
      frequency time firstDistance finalDistance weight mass radius first final) : ℝ :=
  EulerNonuniqueness.General.weightedBoundaryPairDistance radius
    (firstFamily.canonicalExteriorCommonQuadraticCoordinate firstIndex frequency time (diskPhysicalSpectralChart first))
    (firstFamily.canonicalExteriorCommonQuadraticCoordinate firstIndex frequency time (diskPhysicalSpectralChart final))
    (firstFamily.canonicalExteriorCommonTrueAngularCoordinate firstIndex frequency time (diskPhysicalSpectralChart first))
    (firstFamily.canonicalExteriorCommonTrueAngularCoordinate firstIndex frequency time (diskPhysicalSpectralChart final))

def coefficientDifferenceSeries
    (_comparison : CanonicalCommonBoundaryPairAt caps firstFamily finalFamily firstIndex finalIndex
      frequency time firstDistance finalDistance weight mass radius first final) : ℝ :=
  ∑' degree, (96 : ℝ) ^ (degree + 1) *
    ‖firstFamily.canonicalExteriorStaticCoefficient firstIndex time degree - finalFamily.canonicalExteriorStaticCoefficient finalIndex time degree‖

end CanonicalCommonBoundaryPairAt

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
