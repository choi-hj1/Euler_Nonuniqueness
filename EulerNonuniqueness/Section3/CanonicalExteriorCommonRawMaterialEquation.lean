import EulerNonuniqueness.Section3.CanonicalExteriorCommonMaterialField

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorCommonPhysicalCoordinate_hasDerivAt_material_raw {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    (curve finalForce : ℝ → PeriodicC1HolderHalf)
    {frequency left right time distance weight mass speed : ℝ}
    (nonzero : frequency ≠ 0) (member : time ∈ Ioo left right)
    (angularSmall : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate (curve time))‖ < 1 / 2)
    (nearby : ‖diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate (curve time))) 1 - standardCircleBanach‖ < 1 / 3)
    (cutoff : ‖diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate (curve time))) 1 - standardCircleBanach‖ <
      min 1 (2 / (3 * Real.pi)))
    (regular : DifferentiableAt ℝ movingStrainAngularCoefficient
      (diskNeutralCLM (diskPhysicalSpectralCoordinate (curve time))))
    (curveEquation : ∀ current, current ∈ Ioo left right → HasDerivAt curve
      (frequency • diskEulerRotatingField (curve current) + finalForce current) current)
    (inverseActual : ∀ current, current ∈ Ioo left right → HasFDerivAt diskPhysicalSpectralCoordinate
      (diskPhysicalSpectralInverseDerivative (curve current)) (curve current))
    (baseBounds : ∀ current, current ∈ Ioo left right →
      ‖diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate (curve current))) 1‖ < 3 ∧
      ‖fderiv ℝ (fun parameter => diskRelabelCurve parameter 1)
          (diskNeutralCLM (diskPhysicalSpectralCoordinate (curve current)))
          (diskNeutralCLM (diskPhysicalSpectralInverseDerivative (curve current)
            (frequency • diskEulerRotatingField (curve current) + finalForce current)))‖ ≤ speed)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass)
    (small : 192 * (family.patch index).radius ≤ distance)
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
    HasDerivAt (fun current => family.canonicalExteriorCommonPhysicalCoordinate index frequency current (curve current))
      (frequency • diskEulerRotatingField (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) +
        family.canonicalExteriorCommonMaterialResidual index frequency time distance positive
          (by linarith [(family.patch index).radius_positive])
          (family.exterior_domain_gap_of_center_gaps index (centerGaps time member)) (curve time) angularSmall +
        family.canonicalExteriorCommonPhysicalDerivative index frequency time (curve time)
          (finalForce time - family.canonicalProjectedExteriorContourField index time distance positive
            (by linarith [(family.patch index).radius_positive])
            (family.exterior_domain_gap_of_center_gaps index (centerGaps time member))
            (Circle.exp (frequency * time / 2)) (curve time))) time := by
  let angular := fun current => diskNeutralCLM (diskPhysicalSpectralCoordinate (curve current))
  let angularVelocity := fun current => diskNeutralCLM (diskPhysicalSpectralInverseDerivative (curve current)
    (frequency • diskEulerRotatingField (curve current) + finalForce current))
  have angularEquation : ∀ current, current ∈ Ioo left right → HasDerivAt angular (angularVelocity current) current := by
    intro current currentMember
    have actual := (diskNeutralCLM.hasFDerivAt.comp (curve current) (inverseActual current currentMember)).comp_hasDerivAt
      current (curveEquation current currentMember)
    simpa only [ContinuousLinearMap.comp_apply, angular, angularVelocity] using actual
  have moving := family.canonicalExteriorAffineCoordinate_hasDerivAt_common_moving_material index angular angularVelocity
    nonzero member angularSmall (diskNeutralCLM_real _) nearby cutoff angularEquation regular baseBounds
    positive weightNonnegative massNonnegative small inside material centered centerGaps weightBound massBound
    (finalForce time) (curveEquation time member)
  have identity := family.canonicalExteriorCommonMaterialResidual_force_identity index frequency time distance positive
    (by linarith [(family.patch index).radius_positive])
    (family.exterior_domain_gap_of_center_gaps index (centerGaps time member)) (curve time) (finalForce time) angularSmall
  dsimp only at identity
  with_reducible_and_instances
    convert moving using 1
    · simp only [canonicalExteriorCommonPhysicalCoordinate, angular]
    · simpa only [angular, angularVelocity] using identity.symm

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
