import EulerNonuniqueness.Section3.CanonicalExteriorAffinePhaseField
import EulerNonuniqueness.Section3.CanonicalExteriorPrimitiveEquation
import EulerNonuniqueness.Section3.CanonicalPhysicalAmplitudeBound
import EulerNonuniqueness.Section3.DiskChartedRelabelPeriod
import EulerNonuniqueness.General.PhysicalAffineForcingTransform
import EulerNonuniqueness.General.AffinePhaseEvolution
import EulerNonuniqueness.Section3.CanonicalExteriorPrimitiveRawEquation

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem exteriorStrainPhysicalCorrection_hasDerivAt_material {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (angular : PeriodicC1HolderHalf)
    {frequency time distance : ℝ} (nonzero : frequency ≠ 0)
    (inside : ∀ source ∈ Finset.univ.erase index,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ source ∈ Finset.univ.erase index, ∀ label,
      (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label))
    (positive : 0 < distance)
    (centerGaps : ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center time - (family.patch source).center time‖) :
    HasDerivAt (family.exteriorStrainPhysicalCorrection index angular frequency)
      (movingStrainRealCorrectionCLM (diskRelabelCurve angular 1)
          (-Complex.I * family.exteriorStrainModulatedCoefficient index frequency time) +
        family.exteriorStrainAmplitudeCorrection index angular frequency time) time := by
  have coefficientActual := family.exteriorTaylorCoefficient_hasDerivAt_material index 0 inside material positive centerGaps
  unfold exteriorStrainPhysicalCorrection exteriorStrainAmplitudeCorrection exteriorStrainModulatedCoefficient
  generalize baseEq : diskRelabelCurve angular 1 = basePoint
  have actual := movingStrainPhysicalCorrection_hasDerivAt basePoint nonzero coefficientActual
  with_reducible_and_instances
    exact actual

theorem canonicalExteriorAffineCoordinate_hasDerivAt {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    (angular : PeriodicC1HolderHalf) (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
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
    {curve : ℝ → PeriodicC1HolderHalf}
    (curveDerivative : HasDerivAt curve
      (frequency • diskEulerRotatingField (curve time) +
        family.canonicalProjectedExteriorContourField index time distance positive
          (by linarith [(family.patch index).radius_positive])
          (family.exterior_domain_gap_of_center_gaps index (centerGaps time member))
          (Circle.exp (frequency * time / 2)) (curve time)) time) :
    HasDerivAt (fun current => family.canonicalExteriorAffineCoordinate index angular frequency current (curve current))
      (family.canonicalExteriorAffinePhaseField index angular frequency time distance positive
          (by linarith [(family.patch index).radius_positive])
          (family.exterior_domain_gap_of_center_gaps index (centerGaps time member)) (curve time) -
        fixedRelabelEquivalence angular angularSmall
          (family.exteriorAmplitudeDerivativePrimitive index frequency time) -
        family.exteriorStrainAmplitudeCorrection index angular frequency time
          (curve time - diskRelabelCurve angular 1)) time := by
  let base := diskRelabelCurve angular 1
  let primitive := family.relabeledExteriorForcingPrimitive index angular frequency time
  let separation := family.exterior_domain_gap_of_center_gaps index (centerGaps time member)
  have smallEight : 8 * (family.patch index).radius ≤ distance := by
    linarith [(family.patch index).radius_positive]
  let force := family.canonicalProjectedExteriorContourField index time distance positive smallEight separation
    (Circle.exp (frequency * time / 2))
  let amplitudeError := fixedRelabelEquivalence angular angularSmall
    (family.exteriorAmplitudeDerivativePrimitive index frequency time)
  have primitiveDerivative := family.canonicalExteriorForcingPrimitive_hasDerivAt_raw index angular angularSmall realValues
    (nearby.trans_le (min_le_left _ _)) (nearby.trans_le (min_le_right _ _)) nonzero member positive
    weightNonnegative massNonnegative small inside material centered centerGaps weightBound massBound
  have correctionDerivative := family.exteriorStrainPhysicalCorrection_hasDerivAt_material index angular nonzero
    (fun source _ => inside time member source) (fun source _ => material time member source)
    positive (centerGaps time member)
  unfold canonicalExteriorAffineCoordinate canonicalExteriorAffinePhaseField
  dsimp only [base, primitive, force, amplitudeError] at primitiveDerivative correctionDerivative curveDerivative ⊢
  generalize correctionEq : family.exteriorStrainPhysicalCorrection index angular frequency = correctionFunction
    at correctionDerivative ⊢
  generalize primitiveEq : family.relabeledExteriorForcingPrimitive index angular frequency = primitiveFunction
    at primitiveDerivative ⊢
  generalize phaseEq : movingStrainRealCorrectionCLM (diskRelabelCurve angular 1)
    (-Complex.I * family.exteriorStrainModulatedCoefficient index frequency time) = phaseCorrection
    at correctionDerivative ⊢
  generalize amplitudeEq : family.exteriorStrainAmplitudeCorrection index angular frequency time = amplitudeCorrection
    at correctionDerivative ⊢
  generalize errorEq : fixedRelabelEquivalence angular angularSmall
    (family.exteriorAmplitudeDerivativePrimitive index frequency time) = amplitudeValue at primitiveDerivative ⊢
  generalize forceEq : family.canonicalProjectedExteriorContourField index time distance positive smallEight separation
    (Circle.exp (frequency * time / 2)) = forceField at curveDerivative primitiveDerivative ⊢
  generalize baseEq : diskRelabelCurve angular 1 = basePoint at primitiveDerivative ⊢
  with_reducible_and_instances
    exact EulerNonuniqueness.General.affine_phase_evolution_hasDerivAt basePoint
      (diskEulerRotatingField (curve time)) (forceField (curve time))
      (frequency • fderiv ℝ diskEulerRotatingField basePoint (primitiveFunction time) + forceField basePoint)
      amplitudeValue phaseCorrection amplitudeCorrection curveDerivative primitiveDerivative correctionDerivative

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
