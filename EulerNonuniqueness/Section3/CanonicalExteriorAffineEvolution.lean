import EulerNonuniqueness.Section3.CanonicalExteriorAffineMaterialErrorBound
import EulerNonuniqueness.Section3.CanonicalExteriorAffineDerivative
import EulerNonuniqueness.Section3.CanonicalExteriorAffineShift

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

theorem canonicalExteriorAffineCoordinate_exists_uniform_evolution
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
  obtain ⟨errorRadius, errorPositive, constant, constantOne, errors⟩ :=
    canonicalExteriorAffineMaterialError_exists_uniform_bound
  obtain ⟨shiftRadius, shiftPositive, shifts⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_shift_admissibility budget budgetPositive
  let threshold := min (1 / 3) (min 1 (2 / (3 * Real.pi)))
  have thresholdPositive : 0 < threshold := by dsimp [threshold]; positivity
  let radius := min errorRadius (min shiftRadius (threshold / 2))
  have errorLe : radius ≤ errorRadius := min_le_left _ _
  have shiftLe : radius ≤ shiftRadius := (min_le_right _ _).trans (min_le_left _ _)
  have thresholdLe : radius ≤ threshold / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_⟩
  intro count family index angular direction angularSmall angularNear angularMember directionMember realValues
    frequency left right time distance weight mass nonzero member positive weightNonnegative massNonnegative small
    inside material centered centerGaps weightBounds massBounds curve curveValue curveDerivative shapeSmall frequencySmall centroidEqual
  have separated := family.exterior_domain_gap_of_center_gaps index (centerGaps time member)
  have smallFour : 4 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
  have smallFortyEight : 48 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
  have nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < threshold := by
    linarith [norm_nonneg direction, shapeSmall.trans thresholdLe]
  have derivative := family.canonicalExteriorAffineCoordinate_hasDerivAt index angular angularSmall realValues nearby
    nonzero member positive weightNonnegative massNonnegative smallFortyEight inside material centered centerGaps weightBounds massBounds curveDerivative
  have errorActual := errors family index angular direction angularSmall (angularNear.trans errorLe) angularMember directionMember
    realValues nonzero (inside time member index) (material time member index) (centered time member) positive weightNonnegative
    massNonnegative small separated (weightBounds time member) (massBounds time member) (shapeSmall.trans errorLe)
    (frequencySmall.trans errorLe) centroidEqual
  have shiftActual := shifts family index angular direction (angularNear.trans shiftLe) realValues nonzero positive
    weightNonnegative smallFour separated (weightBounds time member) (shapeSmall.trans shiftLe) (frequencySmall.trans shiftLe)
  generalize coordinateEq : family.canonicalExteriorAffineCoordinate index angular frequency = coordinate
    at derivative errorActual shiftActual ⊢
  generalize phaseEq : family.canonicalExteriorAffinePhaseField index angular frequency time distance positive
    (by linarith [(family.patch index).radius_positive]) separated = phaseField at derivative errorActual
  generalize amplitudeEq : fixedRelabelEquivalence angular angularSmall
    (family.exteriorAmplitudeDerivativePrimitive index frequency time) = amplitude at derivative errorActual
  generalize amplitudeOperatorEq : family.exteriorStrainAmplitudeCorrection index angular frequency time = amplitudeOperator
    at derivative errorActual
  generalize baseEq : diskRelabelCurve angular 1 = base at curveValue derivative errorActual shiftActual
  let corrected := fun current => coordinate current (curve current)
  let velocity := phaseField (curve time) - amplitude - amplitudeOperator direction
  let error := velocity - frequency • diskEulerRotatingField (corrected time)
  have derivativeActual : HasDerivAt corrected velocity time := by
    simpa only [corrected, velocity, curveValue, add_sub_cancel_left] using derivative
  have errorBound : ‖error‖ ≤ constant * (weight * ‖direction‖ ^ 2 +
      weight * ((family.patch index).radius / distance) * ‖direction‖ +
      (weight ^ 2 + mass * weight / distance ^ 2) / |frequency|) := by
    simpa only [error, velocity, corrected, curveValue] using errorActual
  have correctedSmall : ‖corrected time - standardCircleBanach‖ ≤ budget := by
    dsimp only [corrected]
    rw [curveValue]
    have triangle : ‖coordinate time (base + direction) - standardCircleBanach‖ ≤
        ‖coordinate time (base + direction) - (base + direction)‖ + ‖base + direction - standardCircleBanach‖ := by
      simpa only [dist_eq_norm] using dist_triangle (coordinate time (base + direction)) (base + direction) standardCircleBanach
    exact triangle.trans (by
      rw [norm_sub_rev]
      linarith [shiftActual])
  refine ⟨error, correctedSmall, ?_, errorBound⟩
  apply derivativeActual.congr_deriv
  dsimp only [error]
  abel

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
