import EulerNonuniqueness.Section3.CanonicalExteriorAffineNamedSlope
import EulerNonuniqueness.Section3.CanonicalInteractionMovingParameter
import EulerNonuniqueness.General.MovingSlopeErrorBudget

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

attribute [local instance] canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero
  canonicalForcingNeg canonicalForcingSub

open EulerNonuniqueness.Section6

theorem canonicalNormalizedInteractionCoordinate_actual_value {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time : ℝ) (data : PeriodicC1HolderHalf) :
    family.canonicalNormalizedInteractionCoordinate index angular frequency time data =
      diskPhysicalScaledGroup frequency (-time) (diskNormalizedQuadraticObservable
        (family.canonicalExteriorAffineCoordinate index angular frequency time data)) := rfl

theorem canonicalExteriorAffineCoordinate_exists_uniform_moving_norm_slope :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular : ℝ → PeriodicC1HolderHalf) (direction angularVelocity : PeriodicC1HolderHalf)
        {frequency left right time distance weight mass : ℝ},
      ‖angular time‖ ≤ radius → angular time ∈ contourContinuousVectorSubmodule →
      direction ∈ contourContinuousVectorSubmodule → frequency ≠ 0 →
      ∀ (member : time ∈ Ioo left right) (positive : 0 < distance), 0 ≤ weight → 0 ≤ mass →
      ∀ (small : 192 * (family.patch index).radius ≤ distance),
      (∀ current ∈ Ioo left right, ∀ label, star ((angular current).val.1 label) = (angular current).val.1 label) →
      HasDerivAt angular angularVelocity time →
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
      ∀ {curve : ℝ → PeriodicC1HolderHalf}, curve time = diskRelabelCurve (angular time) 1 + direction →
      HasDerivAt curve (frequency • diskEulerRotatingField (curve time) +
        family.canonicalProjectedExteriorContourField index time distance positive
          (by linarith [(family.patch index).radius_positive])
          (family.exterior_domain_gap_of_center_gaps index (centerGaps time member))
          (Circle.exp (frequency * time / 2)) (curve time)) time →
      ‖diskRelabelCurve (angular time) 1 - standardCircleBanach‖ + ‖direction‖ ≤ radius →
      weight / |frequency| ≤ radius →
      contourCentroidFunctional (diskRelabelCurve (angular time) 1 + direction) =
        contourCentroidFunctional (diskRelabelCurve (angular time) 1) →
      ∀ threshold : ℝ,
      constant * (|frequency| * ‖diskPhysicalTransverseProjection (diskNormalizedSpectralCoordinate
        (family.canonicalExteriorAffineCoordinate index (angular time) frequency time (curve time)))‖ ^ 3 +
        weight * ‖direction‖ ^ 2 + weight * ((family.patch index).radius / distance) * ‖direction‖ +
        (weight ^ 2 + mass * weight / distance ^ 2) / |frequency| +
        (weight / |frequency|) * ‖angularVelocity‖) < threshold →
      ∀ᶠ later in 𝓝[>] time,
        slope (fun current => ‖family.canonicalNormalizedInteractionCoordinate index (angular current)
          frequency current (curve current)‖) time later < threshold := by
  obtain ⟨fixedRadius, fixedPositive, fixedConstant, fixedOne, fixed⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_named_norm_slope
  obtain ⟨parameterRadius, parameterPositive, parameterConstant, parameterOne, moving⟩ :=
    canonicalNormalizedInteractionCoordinate_exists_uniform_moving_parameter_slope
  let radius := min fixedRadius (min (parameterRadius / 2) (1 / 4))
  let constant := fixedConstant + parameterConstant + 1
  have fixedLe : radius ≤ fixedRadius := min_le_left _ _
  have parameterHalf : radius ≤ parameterRadius / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have parameterLe : radius ≤ parameterRadius := parameterHalf.trans (by linarith)
  have quarterLe : radius ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨radius, by dsimp [radius]; positivity, constant, by dsimp [constant]; linarith, ?_⟩
  intro count family index angular direction angularVelocity frequency left right time distance weight mass
    angularSmall angularMember directionMember nonzero member positive weightNonnegative massNonnegative small
    angularReal angularDerivative inside material centered centerGaps weightBounds massBounds curve curveValue
    curveDerivative shapeSmall frequencySmall centroidEqual
  have angularHalf : ‖angular time‖ < 1 / 2 := (angularSmall.trans quarterLe).trans_lt (by norm_num)
  have curveNear : ‖curve time - standardCircleBanach‖ < parameterRadius :=
    (EulerNonuniqueness.General.norm_sub_reference_le_of_eq_add curveValue).trans_lt
      ((shapeSmall.trans parameterHalf).trans_lt (by linarith))
  have angularNear : ‖angular time‖ < parameterRadius :=
    (angularSmall.trans parameterHalf).trans_lt (by linarith)
  have separated := fun current (currentInside : current ∈ Ioo left right) =>
    family.exterior_domain_gap_of_center_gaps index (centerGaps current currentInside)
  have smallFortyEight : 48 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
  have movingAt := moving family index nonzero member positive weightNonnegative smallFortyEight separated weightBounds
    (frequencySmall.trans parameterLe) curve angular angularVelocity curveDerivative.continuousAt angularDerivative curveNear angularNear angularReal
  have fixedAt := fixed family index (angular time) direction angularHalf (angularSmall.trans fixedLe) angularMember directionMember
    (angularReal time member) nonzero member positive weightNonnegative massNonnegative small inside material centered centerGaps
    weightBounds massBounds (curve := curve)
  generalize sourceEq : family.canonicalProjectedExteriorContourField index time distance positive
    (by linarith [(family.patch index).radius_positive])
    (family.exterior_domain_gap_of_center_gaps index (centerGaps time member)) (Circle.exp (frequency * time / 2)) = source
    at fixedAt curveDerivative
  generalize baseEq : diskRelabelCurve (angular time) 1 = base at fixedAt curveValue shapeSmall centroidEqual
  have fixedReady := fixedAt curveValue curveDerivative (shapeSmall.trans fixedLe) (frequencySmall.trans fixedLe) centroidEqual
  unfold diskNormalizedCubicRate diskNormalizedInteractionNormCurve diskNormalizedInteractionCurve at fixedReady
  simp only [← canonicalNormalizedInteractionCoordinate_actual_value] at fixedReady
  generalize interactionEq : family.canonicalNormalizedInteractionCoordinate index = interaction at fixedReady movingAt ⊢
  generalize transverseEq : diskPhysicalTransverseProjection (diskNormalizedSpectralCoordinate
    (family.canonicalExteriorAffineCoordinate index (angular time) frequency time (curve time))) = transverse at fixedReady ⊢
  intro threshold strict
  let main := |frequency| * ‖transverse‖ ^ 3 + weight * ‖direction‖ ^ 2 +
    weight * ((family.patch index).radius / distance) * ‖direction‖ +
    (weight ^ 2 + mass * weight / distance ^ 2) / |frequency|
  let variation := (weight / |frequency|) * ‖angularVelocity‖
  have radiusNonnegative : 0 ≤ (family.patch index).radius := (family.patch index).radius_positive.le
  have mainNonnegative : 0 ≤ main := by dsimp [main]; positivity
  have variationNonnegative : 0 ≤ variation := by dsimp [variation]; positivity
  have numerical := EulerNonuniqueness.General.moving_slope_error_budget fixedConstant parameterConstant main variation
    (by linarith) (by linarith) mainNonnegative variationNonnegative
  have actualStrict : fixedConstant * main + parameterConstant * variation < threshold := by
    apply numerical.trans_lt
    simpa only [constant, main, variation, add_assoc] using strict
  exact movingAt (fixedConstant * main) threshold
    (fun bound larger => fixedReady bound larger)
    (by simpa only [variation, mul_assoc] using actualStrict)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
