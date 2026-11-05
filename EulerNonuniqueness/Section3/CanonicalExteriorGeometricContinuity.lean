import EulerNonuniqueness.Section6.MovingExteriorPrimitiveContinuity
import EulerNonuniqueness.Section3.CanonicalExteriorAffineCoordinate
import EulerNonuniqueness.Section3.MovingStrainRealCoefficientDerivative
import EulerNonuniqueness.Section3.MovingStrainPhysicalPhaseDerivative
import EulerNonuniqueness.General.OperatorEvaluationContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance geometricAffineContinuityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentRealificationC1Group independentRealificationOutputGroup independentRealificationInputGroup
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

open EulerNonuniqueness.Section6

theorem relabeledExteriorForcingPrimitive_continuousAt_geometric {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    {frequency time distance weight : ℝ} (nonzero : frequency ≠ 0)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (small : 2 * (family.patch index).radius / distance < 1)
    (inside : ∀ source ∈ Finset.univ.erase index,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (centerGaps : ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center time - (family.patch source).center time‖)
    (weightBound : ∀ᶠ current in 𝓝 time, (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) current)
      ((family.patch index).center current) position) ≤ weight) :
    ContinuousAt (family.relabeledExteriorForcingPrimitive index angular frequency) time := by
  have primitive := family.exteriorForcingPrimitive_continuousAt_geometric index nonzero positive
    weightNonnegative small inside centerGaps weightBound
  have transformed := (fixedRelabelEquivalence angular angularSmall).continuous.continuousAt.comp primitive
  apply transformed.congr_of_eventuallyEq
  have near := (eventually_all_finset (Finset.univ.erase index)).mpr
    (fun source member => (family.patch source).eventually_domain_separated_of_center_gap
      (family.patch index).center_continuous (centerGaps source member))
  filter_upwards [near] with current separated
  exact (family.relabeledExteriorForcingPrimitive_fixedRelabel index angular angularSmall realValues
    nonzero positive small separated).symm

theorem exteriorStrainPhysicalCorrection_continuousAt_geometric {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (angular : PeriodicC1HolderHalf)
    {frequency time distance : ℝ} (nonzero : frequency ≠ 0) (positive : 0 < distance)
    (inside : ∀ source ∈ Finset.univ.erase index,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (centerGaps : ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center time - (family.patch source).center time‖) :
    ContinuousAt (family.exteriorStrainPhysicalCorrection index angular frequency) time := by
  have coefficient := family.exteriorTaylorCoefficient_contDiffAt_of_center_gaps 1 index positive inside centerGaps
  have coefficientJet := (coefficient.differentiableAt (by norm_num)).hasDerivAt
  unfold exteriorStrainPhysicalCorrection exteriorStrainModulatedCoefficient
  generalize baseEq : diskRelabelCurve angular 1 = base
  have actual := movingStrainPhysicalCorrection_hasDerivAt base nonzero coefficientJet
  with_reducible_and_instances
    exact actual.continuousAt

theorem canonicalExteriorAffineCoordinate_continuousAt_geometric {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    {frequency time distance weight : ℝ} (nonzero : frequency ≠ 0)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (small : 2 * (family.patch index).radius / distance < 1)
    (inside : ∀ source ∈ Finset.univ.erase index,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (centerGaps : ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center time - (family.patch source).center time‖)
    (weightBound : ∀ᶠ current in 𝓝 time, (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) current)
      ((family.patch index).center current) position) ≤ weight)
    {curve : ℝ → PeriodicC1HolderHalf} (curveContinuous : ContinuousAt curve time) :
    ContinuousAt (fun current => family.canonicalExteriorAffineCoordinate index angular frequency
      current (curve current)) time := by
  have primitive := family.relabeledExteriorForcingPrimitive_continuousAt_geometric index angular angularSmall
    realValues nonzero positive weightNonnegative small inside centerGaps weightBound
  have correctionContinuous := family.exteriorStrainPhysicalCorrection_continuousAt_geometric index angular
    nonzero positive inside centerGaps
  unfold canonicalExteriorAffineCoordinate
  generalize correctionEq : family.exteriorStrainPhysicalCorrection index angular frequency = correction
    at correctionContinuous ⊢
  generalize primitiveEq : family.relabeledExteriorForcingPrimitive index angular frequency = primitiveCurve
    at primitive ⊢
  generalize baseEq : diskRelabelCurve angular 1 = base
  have evaluated := EulerNonuniqueness.General.continuousAt_operator_evaluation
    (curve := fun current => curve current - base)
    correctionContinuous (curveContinuous.sub continuousAt_const)
  exact (curveContinuous.sub primitive).sub evaluated

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
