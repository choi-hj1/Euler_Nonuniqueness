import EulerNonuniqueness.Section3.CanonicalExteriorCommonSourceUniformNorm
import EulerNonuniqueness.Section3.CanonicalExteriorCommonSourceRecipient

noncomputable section

open Metric MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalProjectedExteriorContourField_exists_common_quadratic_source_recipient_ball :
    ∃ rawRadius > 0, ∃ physicalRadius > 0, ∃ spectralRadius > 0, ∃ fieldRadius > 0, ∃ constant ≥ 0,
      ∀ {firstCount finalCount : ℕ} (firstFamily : FiniteMovingPatchFamily firstCount)
        (finalFamily : FiniteMovingPatchFamily finalCount) (firstIndex : Fin firstCount) (finalIndex : Fin finalCount)
        (state : PeriodicC1HolderHalf), state ∈ ball 0 rawRadius →
      ∀ {frequency time firstDistance finalDistance weight : ℝ}, frequency ≠ 0 →
      ∀ (firstPositive : 0 < firstDistance) (finalPositive : 0 < finalDistance), 0 ≤ weight →
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
      ‖firstFamily.canonicalExteriorCommonQuadraticSourceOperator firstIndex frequency time (diskPhysicalSpectralChart state)
        (firstFamily.canonicalProjectedExteriorContourField firstIndex time firstDistance firstPositive
            (by linarith [(firstFamily.patch firstIndex).radius_positive]) firstSeparated
            (Circle.exp (frequency * time / 2)) (diskPhysicalSpectralChart state) -
          finalFamily.canonicalProjectedExteriorContourField finalIndex time finalDistance finalPositive
            (by linarith [(finalFamily.patch finalIndex).radius_positive]) finalSeparated
            (Circle.exp (frequency * time / 2)) (diskPhysicalSpectralChart state))‖ ≤
        constant * (∑' degree, (96 : ℝ) ^ (degree + 1) *
          ‖firstFamily.canonicalExteriorStaticCoefficient firstIndex time degree -
            finalFamily.canonicalExteriorStaticCoefficient finalIndex time degree‖) := by
  obtain ⟨rawRadius, rawPositive, physicalRadius, physicalPositive, spectralRadius, spectralPositive,
    operatorConstant, operatorOne, operators⟩ := canonicalExteriorCommonQuadraticSourceOperator_exists_uniform_norm_ball
  obtain ⟨fieldRadius, fieldPositive, fieldConstant, fieldNonnegative, fields⟩ :=
    canonicalProjectedExteriorContourField_exists_common_source_recipient_ball
  let constant := fieldConstant * operatorConstant
  refine ⟨rawRadius, rawPositive, physicalRadius, physicalPositive, spectralRadius, spectralPositive,
    fieldRadius, fieldPositive, constant, by dsimp only [constant]; positivity, ?_⟩
  intro firstCount finalCount firstFamily finalFamily firstIndex finalIndex state inside frequency time firstDistance finalDistance weight
    nonzero firstPositive finalPositive weightNonnegative firstScale finalScale firstSeparated finalSeparated
    weightBound forcingSmall physicalInside spectralInside fieldInside
  have operatorBound := operators firstFamily firstIndex state inside nonzero firstPositive weightNonnegative firstScale
    firstSeparated weightBound forcingSmall physicalInside spectralInside
  have actual := fields firstFamily finalFamily firstIndex finalIndex time firstDistance finalDistance firstPositive finalPositive
    firstScale finalScale firstSeparated finalSeparated (Circle.exp (frequency * time / 2)) (diskPhysicalSpectralChart state) fieldInside
    (firstFamily.canonicalExteriorCommonQuadraticSourceOperator firstIndex frequency time (diskPhysicalSpectralChart state))
  have seriesNonnegative : 0 ≤ (∑' degree, (96 : ℝ) ^ (degree + 1) *
      ‖firstFamily.canonicalExteriorStaticCoefficient firstIndex time degree -
        finalFamily.canonicalExteriorStaticCoefficient finalIndex time degree‖) :=
    tsum_nonneg (fun degree => mul_nonneg (by positivity) (norm_nonneg _))
  have scalar := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left operatorBound fieldNonnegative) seriesNonnegative
  with_reducible_and_instances
    exact actual.trans scalar

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
