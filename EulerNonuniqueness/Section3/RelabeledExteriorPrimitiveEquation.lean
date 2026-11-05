import EulerNonuniqueness.Section3.RelabeledForcingPrimitiveSeries
import EulerNonuniqueness.Section3.RelabeledExteriorGauge
import EulerNonuniqueness.Section3.FixedRelabelDerivativeConjugacy
import EulerNonuniqueness.Section6.MovingExteriorPrimitiveEquation

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance relabeledExteriorEquationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem relabeledExteriorForcingPrimitive_hasDerivAt_source {count : ℕ}
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
    (massBound : ∀ current ∈ Ioo left right, (∫ position, |family.patchVorticity current index position|) ≤ mass)
    (source : SpatialContourField ((family.patch index).center time) (family.patch index).radius)
    (fieldIdentity : source.field = finiteDomainSourceField (Finset.univ.erase index)
      (fun other => (family.patch other).domain time) family.density) :
    HasDerivAt (family.relabeledExteriorForcingPrimitive index angular frequency)
      (frequency • relabeledDiskDerivative angular
          (family.relabeledExteriorForcingPrimitive index angular frequency time) +
        contourCentroidGaugeProjection (diskRelabelCurve angular 1)
          (source.rawRotatedCompose (diskRelabelCurve angular 1) (Circle.exp (frequency * time / 2))
            (family.patch index).radius_positive (diskRelabelCurve_norm_bound_three angular nearby)) +
        fixedRelabelEquivalence angular angularSmall
          (family.exteriorAmplitudeDerivativePrimitive index frequency time)) time := by
  have radiusPositive := (family.patch index).radius_positive
  have separated : ∀ current ∈ Ioo left right, ∀ other ∈ Finset.univ.erase index,
      ∀ position ∈ (family.patch other).domain current,
        distance ≤ ‖(family.patch index).center current - position‖ := by
    intro current currentMember other otherMember
    exact ((family.patch other).eventually_domain_separated_of_center_gap
      (family.patch index).center_continuous (centerGaps current currentMember other otherMember)).self_of_nhds
  have ratio : 2 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith)
  have relabeled (current : ℝ) (currentMember : current ∈ Ioo left right) :=
    family.relabeledExteriorForcingPrimitive_fixedRelabel index angular angularSmall realValues
      nonzero positive ratio (separated current currentMember)
  have circleDerivative := family.exteriorForcingPrimitive_hasDerivAt_source index nonzero member positive
    weightNonnegative massNonnegative (by linarith) inside material centered centerGaps weightBound massBound
    source fieldIdentity
  let transform := (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap
  have transformed := transform.hasFDerivAt.comp_hasDerivAt time circleDerivative
  have equality : (fun current => transform (family.exteriorForcingPrimitive index frequency current)) =ᶠ[nhds time]
      family.relabeledExteriorForcingPrimitive index angular frequency := by
    filter_upwards [isOpen_Ioo.mem_nhds member] with current currentMember
    exact relabeled current currentMember
  have derivative := transformed.congr_of_eventuallyEq equality.symm
  have generator := congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf =>
    operator (family.exteriorForcingPrimitive index frequency time))
      (relabeledDiskDerivative_intertwines angular angularSmall realValues cutoff)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at generator
  rw [relabeled time member] at generator
  have forcing := exterior_relabeled_gauge_eq_fixedRelabel
    (family.subfamilyVorticity_integrable (Finset.univ.erase index) time)
    (family.subfamilyVorticity_memLp (Finset.univ.erase index) time _) source
    (fieldIdentity.trans (family.finiteDomainSourceField_eq_biotSavart (Finset.univ.erase index) time))
    (Circle.exp (frequency * time / 2)) angular angularSmall realValues nearby radiusPositive positive
    (family.subfamily_support_separated (Finset.univ.erase index) ((family.patch index).center time)
      time distance (separated time member)) ((div_lt_one positive).mpr (by linarith))
  simpa only [transform, map_add, map_smul, ContinuousLinearEquiv.coe_coe, ← generator, ← forcing] using derivative

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
