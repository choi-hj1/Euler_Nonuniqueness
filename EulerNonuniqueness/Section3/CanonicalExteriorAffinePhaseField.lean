import EulerNonuniqueness.Section3.CanonicalExteriorAffineCoordinate
import EulerNonuniqueness.Section3.CanonicalExteriorHigherDifference
import EulerNonuniqueness.Section3.RelabeledPrimitiveLeadingDecomposition
import EulerNonuniqueness.Section3.MovingStrainAffineResidual
import EulerNonuniqueness.Section3.DiskForcingPhaseRotation
import EulerNonuniqueness.General.PhysicalAffineForcingTransform
import EulerNonuniqueness.General.ScaledAffinePhaseAlgebra

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

def canonicalExteriorAffinePhaseField {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time distance : ℝ)
    (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  let base := diskRelabelCurve angular 1
  let force := family.canonicalProjectedExteriorContourField index time distance positive small separated
    (Circle.exp (frequency * time / 2))
  let correction := family.exteriorStrainPhysicalCorrection index angular frequency time
  frequency • diskEulerRotatingField data + force data -
    correction (frequency • diskEulerRotatingField data + force data) -
    (frequency • fderiv ℝ diskEulerRotatingField base
      (family.relabeledExteriorForcingPrimitive index angular frequency time) + force base) -
    movingStrainRealCorrectionCLM base (-Complex.I * family.exteriorStrainModulatedCoefficient index frequency time)
      (data - base)

theorem canonicalExteriorAffinePhaseField_residual_identity {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    {frequency time distance : ℝ} (nonzero : frequency ≠ 0) (positive : 0 < distance)
    (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (data : PeriodicC1HolderHalf) :
    let base := diskRelabelCurve angular 1
    let coefficient := family.exteriorStrainModulatedCoefficient index frequency time
    let primitive := family.relabeledExteriorForcingPrimitive index angular frequency time
    let correction := family.exteriorStrainPhysicalCorrection index angular frequency time
    let higher := family.canonicalExteriorHigherContourField index time distance positive small separated
      (Circle.exp (frequency * time / 2))
    family.canonicalExteriorAffinePhaseField index angular frequency time distance positive small separated data -
        frequency • diskEulerRotatingField (family.canonicalExteriorAffineCoordinate index angular frequency time data) =
      frequency • (diskEulerRotatingField data -
        fderiv ℝ diskEulerRotatingField data (primitive + correction (data - base)) -
        diskEulerRotatingField (family.canonicalExteriorAffineCoordinate index angular frequency time data)) +
      movingStrainAffineResidual base coefficient data + (higher data - higher base) +
      frequency • ((fderiv ℝ diskEulerRotatingField data - fderiv ℝ diskEulerRotatingField base)
        (family.relabeledExteriorHigherForcingPrimitive index angular frequency time)) -
      correction (family.canonicalProjectedExteriorContourField index time distance positive small separated
        (Circle.exp (frequency * time / 2)) data) := by
  let base := diskRelabelCurve angular 1
  let coefficient := family.exteriorStrainModulatedCoefficient index frequency time
  let primitive := family.relabeledExteriorForcingPrimitive index angular frequency time
  let correction := family.exteriorStrainPhysicalCorrection index angular frequency time
  let force := family.canonicalProjectedExteriorContourField index time distance positive small separated
    (Circle.exp (frequency * time / 2))
  let leading := fun current : PeriodicC1HolderHalf => contourCentroidGaugeProjection current (coefficient • c1Conjugate current)
  let generator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf := fderiv ℝ diskEulerRotatingField data
  let baseGenerator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf := fderiv ℝ diskEulerRotatingField base
  let leadingValue := movingStrainRealPrimitiveValue base coefficient
  let partner := movingStrainRealPrimitiveValue base (-Complex.I * coefficient)
  let linear := movingStrainRealCorrectionCLM base coefficient
  let phaseLinear := movingStrainRealCorrectionCLM base (-Complex.I * coefficient)
  have fixedCircle := fixedRelabelEquivalence_circle angular angularSmall realValues
  have valueEquation := movingStrainRealPrimitiveValue_actual_equation angular angularSmall coefficient
    (by simpa only [fixedCircle] using nearby)
  rw [fixedCircle] at valueEquation
  have valueActual : partner = baseGenerator leadingValue + leading base := by
    exact (sub_eq_iff_eq_add.mp valueEquation).trans (add_comm _ _)
  have phaseEquation := EulerNonuniqueness.General.scaled_affine_value_phase_relation nonzero
    baseGenerator primitive leadingValue partner (force base) (leading base) valueActual
  have algebra := EulerNonuniqueness.General.physical_affine_forcing_transform_residual_identity frequency
    (diskEulerRotatingField data)
    (diskEulerRotatingField (family.canonicalExteriorAffineCoordinate index angular frequency time data))
    (force data) (leading data) (force base) (leading base) primitive (frequency⁻¹ • leadingValue)
    (frequency • baseGenerator primitive + force base) partner 0 (data - base)
    generator baseGenerator correction phaseLinear 0 phaseEquation
  have correctionIdentity : correction = frequency⁻¹ • linear := by
    with_reducible_and_instances
      exact family.exteriorStrainPhysicalCorrection_eq_smul index angular frequency time
  have scaledLeading := EulerNonuniqueness.General.scaled_affine_leading_residual nonzero
    generator linear phaseLinear (leading data) (diskEulerRotatingField data) leadingValue partner (data - base)
  rw [correctionIdentity] at algebra
  rw [scaledLeading] at algebra
  have ratio : 2 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive])
  have tailIdentity := family.relabeledExteriorHigherForcingPrimitive_eq_sub_leading index angular angularSmall
    realValues nonzero positive separated ratio
  have higherIdentity (current : PeriodicC1HolderHalf) :
      family.canonicalExteriorHigherContourField index time distance positive small separated
        (Circle.exp (frequency * time / 2)) current = force current - leading current := by
    unfold canonicalExteriorHigherContourField
    rw [diskForcingPhase_eq_rotation_power 0 frequency time]
    rfl
  simp only [sub_zero, ContinuousLinearMap.zero_apply] at algebra
  change family.canonicalExteriorAffinePhaseField index angular frequency time distance positive small separated data -
      frequency • diskEulerRotatingField (family.canonicalExteriorAffineCoordinate index angular frequency time data) = _
  rw [higherIdentity, higherIdentity, tailIdentity]
  unfold canonicalExteriorAffinePhaseField movingStrainAffineResidual canonicalExteriorAffineCoordinate
  unfold canonicalExteriorAffineCoordinate at algebra
  dsimp only [base, coefficient, primitive, correction, force, leading, generator, baseGenerator,
    leadingValue, partner, linear, phaseLinear] at *
  unfold exteriorStrainPhysicalCorrection at *
  generalize baseEq : diskRelabelCurve angular 1 = basePoint at *
  with_reducible_and_instances
    simpa only [exteriorStrainModulatedCoefficient, add_assoc] using algebra

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
