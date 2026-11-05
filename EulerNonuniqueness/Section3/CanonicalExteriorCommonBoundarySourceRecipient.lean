import EulerNonuniqueness.Section3.CanonicalExteriorCommonQuadraticSourceRecipient
import EulerNonuniqueness.Section3.CanonicalExteriorCommonTrueAngularSourceNorm

noncomputable section

open Metric MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalProjectedExteriorContourField_exists_common_boundary_source_recipient_ball :
    ∃ rawRadius > 0, ∃ physicalRadius > 0, ∃ spectralRadius > 0, ∃ fieldRadius > 0, ∃ constant ≥ 0,
      ∀ {firstCount finalCount : ℕ} (firstFamily : FiniteMovingPatchFamily firstCount)
        (finalFamily : FiniteMovingPatchFamily finalCount) (firstIndex : Fin firstCount) (finalIndex : Fin finalCount)
        (state : PeriodicC1HolderHalf), state ∈ ball 0 rawRadius →
      ∀ {frequency time firstDistance finalDistance weight neutralWeight : ℝ}, frequency ≠ 0 →
      ∀ (firstPositive : 0 < firstDistance) (finalPositive : 0 < finalDistance), 0 ≤ weight →
      0 ≤ neutralWeight → neutralWeight ≤ 1 →
      ∀ (firstScale : 192 * (firstFamily.patch firstIndex).radius ≤ firstDistance)
        (finalScale : 192 * (finalFamily.patch finalIndex).radius ≤ finalDistance)
        (firstSeparated : ∀ source ∈ Finset.univ.erase firstIndex, ∀ position ∈ (firstFamily.patch source).domain time,
          firstDistance ≤ ‖(firstFamily.patch firstIndex).center time - position‖)
        (finalSeparated : ∀ source ∈ Finset.univ.erase finalIndex, ∀ position ∈ (finalFamily.patch source).domain time,
          finalDistance ≤ ‖(finalFamily.patch finalIndex).center time - position‖),
      (∫ position, inverseSquareVorticityWeight
        (firstFamily.subfamilyVorticity (Finset.univ.erase firstIndex) time) ((firstFamily.patch firstIndex).center time) position) ≤ weight →
      weight / |frequency| ≤ 1 →
      ‖firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart state) - standardCircleBanach‖ ≤ physicalRadius →
      ‖firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart state)‖ ≤ spectralRadius →
      ‖diskPhysicalSpectralChart state - standardCircleBanach‖ ≤ fieldRadius →
      let sourceDifference := firstFamily.canonicalProjectedExteriorContourField firstIndex time firstDistance firstPositive
          (by linarith [(firstFamily.patch firstIndex).radius_positive]) firstSeparated
          (Circle.exp (frequency * time / 2)) (diskPhysicalSpectralChart state) -
        finalFamily.canonicalProjectedExteriorContourField finalIndex time finalDistance finalPositive
          (by linarith [(finalFamily.patch finalIndex).radius_positive]) finalSeparated
          (Circle.exp (frequency * time / 2)) (diskPhysicalSpectralChart state)
      ‖firstFamily.canonicalExteriorCommonQuadraticSourceOperator firstIndex frequency time (diskPhysicalSpectralChart state) sourceDifference‖ +
        neutralWeight * ‖firstFamily.canonicalExteriorCommonTrueAngularSourceOperator firstIndex frequency time (diskPhysicalSpectralChart state) sourceDifference‖ ≤
      constant * (∑' degree, (96 : ℝ) ^ (degree + 1) *
        ‖firstFamily.canonicalExteriorStaticCoefficient firstIndex time degree -
          finalFamily.canonicalExteriorStaticCoefficient finalIndex time degree‖) := by
  obtain ⟨quadraticRawRadius, quadraticRawPositive, quadraticPhysicalRadius, quadraticPhysicalPositive,
    spectralRadius, spectralPositive, quadraticFieldRadius, quadraticFieldPositive, quadraticConstant, quadraticNonnegative, quadratics⟩ :=
    canonicalProjectedExteriorContourField_exists_common_quadratic_source_recipient_ball
  obtain ⟨angularRawRadius, angularRawPositive, angularPhysicalRadius, angularPhysicalPositive,
    angularConstant, angularOne, angulars⟩ := canonicalExteriorCommonTrueAngularSourceOperator_exists_uniform_norm_ball
  obtain ⟨angularFieldRadius, angularFieldPositive, fieldConstant, fieldNonnegative, fields⟩ :=
    canonicalProjectedExteriorContourField_exists_common_source_recipient_ball
  let constant := quadraticConstant + fieldConstant * angularConstant
  have angularNonnegative : 0 ≤ angularConstant := by linarith
  refine ⟨min quadraticRawRadius angularRawRadius, lt_min quadraticRawPositive angularRawPositive,
    min quadraticPhysicalRadius angularPhysicalRadius, lt_min quadraticPhysicalPositive angularPhysicalPositive,
    spectralRadius, spectralPositive, min quadraticFieldRadius angularFieldRadius, lt_min quadraticFieldPositive angularFieldPositive,
    constant, by dsimp only [constant]; positivity, ?_⟩
  intro firstCount finalCount firstFamily finalFamily firstIndex finalIndex state inside frequency time firstDistance finalDistance weight neutralWeight
    nonzero firstPositive finalPositive weightNonnegative neutralNonnegative neutralSmall firstScale finalScale firstSeparated finalSeparated
    weightBound forcingSmall physicalInside spectralInside fieldInside
  dsimp only
  have quadratic := quadratics firstFamily finalFamily firstIndex finalIndex state (ball_subset_ball (min_le_left _ _) inside)
    nonzero firstPositive finalPositive weightNonnegative firstScale finalScale firstSeparated finalSeparated weightBound forcingSmall
    (physicalInside.trans (min_le_left _ _)) spectralInside (fieldInside.trans (min_le_left _ _))
  have angular := angulars firstFamily firstIndex state (ball_subset_ball (min_le_right _ _) inside)
    nonzero firstPositive weightNonnegative firstScale firstSeparated weightBound forcingSmall (physicalInside.trans (min_le_right _ _))
  have field := fields firstFamily finalFamily firstIndex finalIndex time firstDistance finalDistance firstPositive finalPositive
    firstScale finalScale firstSeparated finalSeparated (Circle.exp (frequency * time / 2)) (diskPhysicalSpectralChart state)
    (fieldInside.trans (min_le_right _ _))
    (firstFamily.canonicalExteriorCommonTrueAngularSourceOperator firstIndex frequency time (diskPhysicalSpectralChart state))
  let series := ∑' degree, (96 : ℝ) ^ (degree + 1) *
    ‖firstFamily.canonicalExteriorStaticCoefficient firstIndex time degree - finalFamily.canonicalExteriorStaticCoefficient finalIndex time degree‖
  have seriesNonnegative : 0 ≤ series := tsum_nonneg (fun degree => mul_nonneg (by positivity) (norm_nonneg _))
  have angularBound := field.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left angular fieldNonnegative) seriesNonnegative)
  have scaled := (mul_le_mul_of_nonneg_left angularBound neutralNonnegative).trans
    (mul_le_of_le_one_left (by positivity : 0 ≤ fieldConstant * angularConstant * series) neutralSmall)
  with_reducible_and_instances
    calc
      _ ≤ quadraticConstant * series + fieldConstant * angularConstant * series := add_le_add quadratic scaled
      _ = _ := by dsimp only [constant]; ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
