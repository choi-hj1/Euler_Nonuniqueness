import EulerNonuniqueness.Section3.CanonicalExteriorContourForcing
import EulerNonuniqueness.Section3.RelabeledExteriorPrimitiveEquation

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance canonicalPrimitiveEquationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem exterior_domain_gap_of_center_gaps {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time distance : ℝ}
    (centerGaps : ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center time - (family.patch source).center time‖) :
    ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖ := by
  intro source sourceMember
  exact ((family.patch source).eventually_domain_separated_of_center_gap
    (family.patch index).center_continuous (centerGaps source sourceMember)).self_of_nhds

theorem canonicalExteriorForcingPrimitive_hasDerivAt {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    (angular : PeriodicC1HolderHalf) (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 1 / 3)
    (cutoff : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {frequency left right time distance weight mass : ℝ}
    (nonzero : frequency ≠ 0) (member : time ∈ Ioo left right)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass)
    (small : 48 * (family.patch index).radius ≤ distance)
    (inside : ∀ current ∈ Ioo left right, ∀ source,
      current ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ current ∈ Ioo left right, ∀ source label,
      (family.patch source).boundaryVelocity current label =
        biotSavart (family.vorticity current) ((family.patch source).boundary current label))
    (centered : ∀ current ∈ Ioo left right,
      (family.patch index).center =ᶠ[nhds current] (family.patch index).centroid)
    (centerGaps : ∀ current ∈ Ioo left right, ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center current - (family.patch source).center current‖)
    (weightBound : ∀ current ∈ Ioo left right, (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) current) ((family.patch index).center current) position) ≤ weight)
    (massBound : ∀ current ∈ Ioo left right, (∫ position, |family.patchVorticity current index position|) ≤ mass) :
    HasDerivAt (family.relabeledExteriorForcingPrimitive index angular frequency)
      (frequency • relabeledDiskDerivative angular
          (family.relabeledExteriorForcingPrimitive index angular frequency time) +
        contourCentroidGaugeProjection (diskRelabelCurve angular 1)
          (family.canonicalExteriorContourForcing index time distance positive
            (by linarith [(family.patch index).radius_positive])
            (family.exterior_domain_gap_of_center_gaps index (centerGaps time member))
            (diskRelabelCurve angular 1) (diskRelabelCurve_norm_bound_three angular nearby)
            (Circle.exp (frequency * time / 2))) +
        fixedRelabelEquivalence angular angularSmall
          (family.exteriorAmplitudeDerivativePrimitive index frequency time)) time := by
  let separation := family.exterior_domain_gap_of_center_gaps index (centerGaps time member)
  have smallEight : 8 * (family.patch index).radius ≤ distance := by
    linarith [(family.patch index).radius_positive]
  let source := family.canonicalExteriorSpatialContourField index time distance positive smallEight separation
  exact family.relabeledExteriorForcingPrimitive_hasDerivAt_source index angular angularSmall realValues
    nearby cutoff nonzero member positive weightNonnegative massNonnegative small inside material centered
    centerGaps weightBound massBound source rfl

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
