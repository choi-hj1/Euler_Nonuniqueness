import EulerNonuniqueness.Section3.CanonicalExteriorMovingAngularPrimitive
import EulerNonuniqueness.Section3.CanonicalExteriorMovingAngularCorrection
import EulerNonuniqueness.General.CommonMovingAffinePhaseEvolution

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd

open EulerNonuniqueness.Section6

theorem canonicalExteriorAffineCoordinate_hasDerivAt_common_moving_material {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    (angular angularVelocity : ℝ → PeriodicC1HolderHalf)
    {frequency left right time distance weight mass speed : ℝ}
    (nonzero : frequency ≠ 0) (member : time ∈ Ioo left right)
    (angularSmall : ‖angular time‖ < 1 / 2)
    (realValues : ∀ label, star ((angular time).val.1 label) = (angular time).val.1 label)
    (nearby : ‖diskRelabelCurve (angular time) 1 - standardCircleBanach‖ < 1 / 3)
    (cutoff : ‖diskRelabelCurve (angular time) 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (angularEquation : ∀ current, current ∈ Ioo left right → HasDerivAt angular (angularVelocity current) current)
    (regular : DifferentiableAt ℝ movingStrainAngularCoefficient (angular time))
    (baseBounds : ∀ current, current ∈ Ioo left right →
      ‖diskRelabelCurve (angular current) 1‖ < 3 ∧
      ‖fderiv ℝ (fun parameter => diskRelabelCurve parameter 1) (angular current) (angularVelocity current)‖ ≤ speed)
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
    (massBound : ∀ current ∈ Ioo left right, (∫ position, |family.patchVorticity current index position|) ≤ mass)
    {curve : ℝ → PeriodicC1HolderHalf} (finalForce : PeriodicC1HolderHalf)
    (curveEquation : HasDerivAt curve
      (frequency • diskEulerRotatingField (curve time) + finalForce) time) :
    HasDerivAt (fun current => family.canonicalExteriorAffineCoordinate index (angular current) frequency current (curve current))
      (family.canonicalExteriorAffinePhaseField index (angular time) frequency time distance positive
          (by linarith [(family.patch index).radius_positive])
          (family.exterior_domain_gap_of_center_gaps index (centerGaps time member)) (curve time) -
        fixedRelabelEquivalence (angular time) angularSmall
          (family.exteriorAmplitudeDerivativePrimitive index frequency time) -
        family.exteriorStrainAmplitudeCorrection index (angular time) frequency time
          (curve time - diskRelabelCurve (angular time) 1) +
        family.canonicalExteriorAffineAngularDerivative index (angular time) frequency time (curve time)
          (angularVelocity time) +
        (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf -
          family.exteriorStrainPhysicalCorrection index (angular time) frequency time)
          (finalForce - family.canonicalProjectedExteriorContourField index time distance positive
            (by linarith [(family.patch index).radius_positive])
            (family.exterior_domain_gap_of_center_gaps index (centerGaps time member))
            (Circle.exp (frequency * time / 2)) (curve time))) time := by
  have primitiveActual := family.canonicalExteriorForcingPrimitive_hasDerivAt_moving_angular_raw
    index angular angularVelocity nonzero member angularSmall realValues nearby cutoff angularEquation baseBounds
    positive weightNonnegative massNonnegative small inside material centered centerGaps weightBound massBound
  have correctionActual := family.exteriorStrainPhysicalCorrection_hasDerivAt_moving_angular_material
    index nonzero (angularEquation time member) regular (fun source _ => inside time member source)
    (fun source _ => material time member source) positive (centerGaps time member)
  have baseActual := (diskRelabelMap_analyticAt (angular time)).differentiableAt.hasFDerivAt.comp_hasDerivAt
    time (angularEquation time member)
  let firstForce := family.canonicalProjectedExteriorContourField index time distance positive
    (by linarith [(family.patch index).radius_positive])
    (family.exterior_domain_gap_of_center_gaps index (centerGaps time member))
    (Circle.exp (frequency * time / 2))
  have actual := EulerNonuniqueness.General.common_moving_affine_phase_evolution_hasDerivAt
    (diskEulerRotatingField (curve time)) (firstForce (curve time)) finalForce
    (frequency • fderiv ℝ diskEulerRotatingField (diskRelabelCurve (angular time) 1)
      (family.relabeledExteriorForcingPrimitive index (angular time) frequency time) +
      firstForce (diskRelabelCurve (angular time) 1))
    (fixedRelabelEquivalence (angular time) angularSmall
      (family.exteriorAmplitudeDerivativePrimitive index frequency time))
    (relabeledPrimitiveAngularDerivative frequency
      (fun degree => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
        (family.patch index).radius (degree + 1)) time (angular time) (angularVelocity time))
    (movingStrainRealCorrectionCLM (diskRelabelCurve (angular time) 1)
      (-Complex.I * family.exteriorStrainModulatedCoefficient index frequency time))
    (family.exteriorStrainAmplitudeCorrection index (angular time) frequency time)
    (frequency⁻¹ • movingStrainAngularCorrectionDerivative (angular time)
      (family.exteriorStrainModulatedCoefficient index frequency time) (angularVelocity time))
    (fderiv ℝ (fun parameter => diskRelabelCurve parameter 1) (angular time) (angularVelocity time))
    curveEquation baseActual primitiveActual correctionActual
  with_reducible_and_instances
    convert (config := { transparency := .all }) actual using 1
    all_goals first
      | (change (_ : TopologicalSpace PeriodicC1HolderHalf) = _; with_unfolding_all rfl)
      | (funext current; simp only [canonicalExteriorAffineCoordinate, Function.comp_def])
      | (simp only [canonicalExteriorAffinePhaseField, canonicalExteriorAffineAngularDerivative_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, Function.comp_def, firstForce] <;> abel)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
