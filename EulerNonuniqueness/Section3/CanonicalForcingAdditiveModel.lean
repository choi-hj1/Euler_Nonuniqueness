import EulerNonuniqueness.Section3.CanonicalExteriorNormalizedEvolution
import EulerNonuniqueness.Section3.DiskNormalizedFlatErrorSlope

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

local instance canonicalForcingAddCommGroup : AddCommGroup PeriodicC1HolderHalf :=
  normalizedUniformSlopeC1Group.toAddCommGroup

local instance canonicalForcingAdd : Add PeriodicC1HolderHalf := canonicalForcingAddCommGroup.toAdd
local instance canonicalForcingZero : Zero PeriodicC1HolderHalf := canonicalForcingAddCommGroup.toZero
local instance canonicalForcingNeg : Neg PeriodicC1HolderHalf := canonicalForcingAddCommGroup.toNeg
local instance canonicalForcingSub : Sub PeriodicC1HolderHalf := canonicalForcingAddCommGroup.toSub

theorem diskNormalizedQuadraticObservable_exists_uniform_canonical_error_slope :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {curve : ℝ → PeriodicC1HolderHalf} {time frequency errorConstant first second third : ℝ}
        {error : PeriodicC1HolderHalf},
      1 ≤ errorConstant → ‖curve time - standardCircleBanach‖ ≤ radius →
      HasDerivAt curve (frequency • diskEulerRotatingField (curve time) + error) time →
      ‖error‖ ≤ errorConstant * (first + second + third) →
      ∀ threshold, (constant * errorConstant) *
        (|frequency| * ‖diskPhysicalTransverseProjection
          (diskNormalizedSpectralCoordinate (curve time))‖ ^ 3 + first + second + third) < threshold →
      ∀ᶠ later in 𝓝[>] time,
        slope (fun current => ‖diskPhysicalScaledGroup frequency (-current)
          (diskNormalizedQuadraticObservable (curve current))‖) time later < threshold := by
  with_reducible_and_instances
    exact diskNormalizedQuadraticObservable_exists_uniform_flat_error_slope

namespace FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem canonicalExteriorAffineCoordinate_exists_uniform_canonical_evolution
    (budget : ℝ) (budgetPositive : 0 < budget) :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular direction : PeriodicC1HolderHalf) (angularSmall : ‖angular‖ < 1 / 2), ‖angular‖ ≤ radius →
      angular ∈ contourContinuousVectorSubmodule → direction ∈ contourContinuousVectorSubmodule →
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ {frequency left right time distance weight mass : ℝ}, frequency ≠ 0 →
      ∀ (member : time ∈ Ioo left right) (positive : 0 < distance), 0 ≤ weight → 0 ≤ mass →
      ∀ (small : 192 * (family.patch index).radius ≤ distance),
      (∀ current ∈ Ioo left right, ∀ source,
        current ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
      (∀ current ∈ Ioo left right, ∀ source label,
        (family.patch source).boundaryVelocity current label =
          biotSavart (family.vorticity current) ((family.patch source).boundary current label)) →
      (∀ current ∈ Ioo left right, (family.patch index).center =ᶠ[nhds current] (family.patch index).centroid) →
      ∀ (centerGaps : ∀ current ∈ Ioo left right, ∀ source ∈ Finset.univ.erase index,
        distance + 3 * (family.patch source).radius ≤
          ‖(family.patch index).center current - (family.patch source).center current‖),
      (∀ current ∈ Ioo left right, (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) current) ((family.patch index).center current) position) ≤ weight) →
      (∀ current ∈ Ioo left right, (∫ position, |family.patchVorticity current index position|) ≤ mass) →
      ∀ {curve : ℝ → PeriodicC1HolderHalf}, curve time = diskRelabelCurve angular 1 + direction →
      HasDerivAt curve (frequency • diskEulerRotatingField (curve time) +
        family.canonicalProjectedExteriorContourField index time distance positive
          (by linarith [(family.patch index).radius_positive])
          (family.exterior_domain_gap_of_center_gaps index (centerGaps time member))
          (Circle.exp (frequency * time / 2)) (curve time)) time →
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖direction‖ ≤ radius → weight / |frequency| ≤ radius →
      contourCentroidFunctional (diskRelabelCurve angular 1 + direction) = contourCentroidFunctional (diskRelabelCurve angular 1) →
      let corrected := fun current => family.canonicalExteriorAffineCoordinate index angular frequency current (curve current)
      ∃ error : PeriodicC1HolderHalf,
        ‖corrected time - standardCircleBanach‖ ≤ budget ∧
        HasDerivAt corrected (frequency • diskEulerRotatingField (corrected time) + error) time ∧
        ‖error‖ ≤ constant * (weight * ‖direction‖ ^ 2 +
          weight * ((family.patch index).radius / distance) * ‖direction‖ +
          (weight ^ 2 + mass * weight / distance ^ 2) / |frequency|) := by
  with_reducible_and_instances
    exact canonicalExteriorAffineCoordinate_exists_uniform_normalized_evolution budget budgetPositive

end FiniteMovingPatchFamily
end EulerNonuniqueness.Paper

