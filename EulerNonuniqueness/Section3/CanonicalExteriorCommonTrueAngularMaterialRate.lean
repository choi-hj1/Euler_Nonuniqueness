import EulerNonuniqueness.Section3.CanonicalExteriorCommonMaterialActualRate
import EulerNonuniqueness.Section3.CanonicalExteriorCommonMaterialAbsolute
import EulerNonuniqueness.Section3.CanonicalExteriorCommonPhysicalPair
import EulerNonuniqueness.Section3.DiskNormalizedTrueAngularErrorRelative

noncomputable section

open Filter Metric MeasureTheory Set
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

def canonicalExteriorCommonTrueAngularMaterialResidual {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time distance : ℝ) (positive : 0 < distance)
    (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (data : PeriodicC1HolderHalf) (angularSmall : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate data)‖ < 1 / 2) :
    PeriodicC1HolderHalf :=
  diskNormalizedTrueAngularError (family.canonicalExteriorCommonPhysicalCoordinate index frequency time data)
    (family.canonicalExteriorCommonMaterialResidual index frequency time distance positive small separated data angularSmall)

theorem canonicalExteriorCommonTrueAngularMaterialResidual_exists_actual_quadratic_rate_ball :
    ∃ rawRadius > 0, ∃ correctedRadius > 0, ∃ forcingRadius > 0, ∃ shapeRadius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (first final : PeriodicC1HolderHalf), first ∈ ball 0 rawRadius → final ∈ ball 0 rawRadius →
      first ∈ contourContinuousVectorSubmodule → final ∈ contourContinuousVectorSubmodule →
      diskPhysicalSpectralChart first ∈ contourContinuousVectorSubmodule →
      diskPhysicalSpectralChart final ∈ contourContinuousVectorSubmodule →
      diskSpectralTubularArea first = Real.pi → diskSpectralTubularArea final = Real.pi →
      contourCentroidFunctional (diskPhysicalSpectralChart first) = 0 →
      contourCentroidFunctional (diskPhysicalSpectralChart final) = 0 →
      ∀ (firstSmall : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart first))‖ < 1 / 2)
        (finalSmall : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart final))‖ < 1 / 2),
      ∀ {frequency time distance weight mass radius : ℝ}, frequency ≠ 0 →
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime →
      (∀ label, (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) →
      (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid →
      ∀ (positive : 0 < distance) (weightNonnegative : 0 ≤ weight),
      0 ≤ mass → 0 ≤ radius → radius ≤ shapeRadius →
      ‖diskPhysicalTransverseProjection first‖ ≤ radius → ‖diskPhysicalTransverseProjection final‖ ≤ radius →
      ∀ (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖),
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      (∫ position, |family.patchVorticity time index position|) ≤ mass →
      weight / |frequency| ≤ forcingRadius → weight / |frequency| ≤ radius →
      (weight / |frequency|) ^ 2 ≤ radius ^ 3 →
      (weight / |frequency|) * ((family.patch index).radius / distance) ≤ radius ^ 2 →
      (12 * (46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2))) / |frequency| ≤
        |frequency| * radius ^ 3 →
      ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart first) - standardCircleBanach‖ ≤ correctedRadius →
      ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart final) - standardCircleBanach‖ ≤ correctedRadius →
      ‖family.canonicalExteriorCommonTrueAngularMaterialResidual index frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart first) firstSmall -
        family.canonicalExteriorCommonTrueAngularMaterialResidual index frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart final) finalSmall‖ ≤
        constant * |frequency| * radius ^ 2 *
          (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
            radius * ‖diskNeutralCLM first - diskNeutralCLM final‖) := by
  obtain ⟨pairRadius, pairPositive, pairForcingRadius, pairForcingPositive, shapeRadius, shapePositive,
    pairConstant, pairOne, pairs⟩ := canonicalExteriorCommonMaterialResidual_exists_actual_quadratic_rate_ball
  obtain ⟨absoluteRadius, absolutePositive, absoluteForcingRadius, absoluteForcingPositive,
    absoluteConstant, absoluteOne, absolutes⟩ := canonicalExteriorCommonMaterialResidual_exists_actual_cubic_bound_ball
  obtain ⟨physicalRadius, physicalPositive, physicalConstant, physicalOne, physicals⟩ :=
    canonicalExteriorCommonPhysicalCoordinate_exists_raw_pair_ball
  obtain ⟨correctedRadius, correctedPositive, normalConstant, normalOne, normals⟩ :=
    diskNormalizedTrueAngularError_exists_uniform_pair_ball
  let rawRadius := min pairRadius (min absoluteRadius physicalRadius)
  let constant := normalConstant * (pairConstant + physicalConstant * absoluteConstant) + 1
  have pairNonnegative : 0 ≤ pairConstant := by linarith
  have physicalNonnegative : 0 ≤ physicalConstant := by linarith
  have absoluteNonnegative : 0 ≤ absoluteConstant := by linarith
  have normalNonnegative : 0 ≤ normalConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ normalConstant * (pairConstant + physicalConstant * absoluteConstant) := by positivity
    dsimp only [constant]
    linarith
  refine ⟨rawRadius, by dsimp only [rawRadius]; positivity, correctedRadius, correctedPositive,
    min pairForcingRadius absoluteForcingRadius, lt_min pairForcingPositive absoluteForcingPositive,
    min shapeRadius 1, lt_min shapePositive (by norm_num), constant, constantOne, ?_⟩
  intro count family index first final firstInside finalInside firstMember finalMember firstPhysicalMember finalPhysicalMember
    firstArea finalArea firstCentered finalCentered firstSmall finalSmall frequency time distance weight mass radius nonzero
    timeInside material centered positive weightNonnegative massNonnegative radiusNonnegative radiusSmall firstTransverse finalTransverse
    small separated weightBound massBound forcingSmall epsilonSmall squaredSmall tailSmall derivativeScale firstCorrected finalCorrected
  have radiusOne := radiusSmall.trans (min_le_right _ _)
  have materialPair := pairs family index first final (ball_subset_ball (min_le_left _ _) firstInside)
    (ball_subset_ball (min_le_left _ _) finalInside) firstMember finalMember firstPhysicalMember finalPhysicalMember
    firstArea finalArea firstCentered finalCentered firstSmall finalSmall nonzero timeInside material centered positive weightNonnegative
    massNonnegative radiusNonnegative (radiusSmall.trans (min_le_left _ _)) firstTransverse finalTransverse small separated weightBound
    massBound (forcingSmall.trans (min_le_left _ _)) epsilonSmall squaredSmall tailSmall derivativeScale
  have materialFinal := absolutes family index final
    (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) finalInside) finalMember finalPhysicalMember
    finalArea finalCentered finalSmall nonzero timeInside material centered positive weightNonnegative massNonnegative
    radiusNonnegative radiusOne finalTransverse small separated weightBound massBound
    (forcingSmall.trans (min_le_right _ _)) epsilonSmall squaredSmall tailSmall derivativeScale
  have physicalPair := physicals family index first final
    (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) firstInside)
    (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) finalInside)
    firstArea finalArea nonzero positive weightNonnegative small separated weightBound (epsilonSmall.trans radiusOne)
  have actual := normals
    (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart first))
    (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart final))
    (family.canonicalExteriorCommonMaterialResidual index frequency time distance positive
      (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart first) firstSmall)
    (family.canonicalExteriorCommonMaterialResidual index frequency time distance positive
      (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart final) finalSmall)
    firstCorrected finalCorrected
  have bounded := actual.trans (mul_le_mul_of_nonneg_left (add_le_add materialPair
    (mul_le_mul physicalPair materialFinal (norm_nonneg _) (by positivity))) normalNonnegative)
  let transverse := ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖
  let angular := ‖diskNeutralCLM first - diskNeutralCLM final‖
  have transverseNonnegative : 0 ≤ transverse := norm_nonneg _
  have angularNonnegative : 0 ≤ angular := norm_nonneg _
  have weighted : radius * (transverse + angular) ≤ transverse + radius * angular := by
    nlinarith [mul_le_mul_of_nonneg_right radiusOne transverseNonnegative]
  have weightedScaled := mul_le_mul_of_nonneg_left weighted
    (by positivity : 0 ≤ physicalConstant * absoluteConstant * |frequency| * radius ^ 2)
  have combined : pairConstant * |frequency| * radius ^ 2 * (transverse + radius * angular) +
      (physicalConstant * (transverse + angular)) * (absoluteConstant * |frequency| * radius ^ 3) ≤
      (pairConstant + physicalConstant * absoluteConstant) * |frequency| * radius ^ 2 * (transverse + radius * angular) := by
    nlinarith only [weightedScaled]
  have coefficientLe : normalConstant * (pairConstant + physicalConstant * absoluteConstant) ≤ constant := by
    dsimp only [constant]
    linarith
  have scalar := mul_le_mul_of_nonneg_right coefficientLe
    (by positivity : 0 ≤ |frequency| * radius ^ 2 * (transverse + radius * angular))
  with_reducible_and_instances
    calc
      _ ≤ normalConstant * ((pairConstant + physicalConstant * absoluteConstant) * |frequency| * radius ^ 2 *
          (transverse + radius * angular)) := bounded.trans (mul_le_mul_of_nonneg_left combined normalNonnegative)
      _ = (normalConstant * (pairConstant + physicalConstant * absoluteConstant)) *
          (|frequency| * radius ^ 2 * (transverse + radius * angular)) := by ring
      _ ≤ constant * (|frequency| * radius ^ 2 * (transverse + radius * angular)) := scalar
      _ = _ := by ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily

