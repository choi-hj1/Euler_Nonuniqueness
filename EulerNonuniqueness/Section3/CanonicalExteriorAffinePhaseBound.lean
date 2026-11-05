import EulerNonuniqueness.Section3.CanonicalExteriorAffineErrorBudget
import EulerNonuniqueness.Section3.CanonicalExteriorAffinePhaseField
import EulerNonuniqueness.General.FiveTermNormBound

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorAffinePhaseField_exists_uniform_error_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular direction : PeriodicC1HolderHalf), ‖angular‖ ≤ radius →
      angular ∈ contourContinuousVectorSubmodule → direction ∈ contourContinuousVectorSubmodule →
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ {frequency time distance weight : ℝ} (nonzero : frequency ≠ 0) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
        (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖)
        (weightBound : (∫ position, inverseSquareVorticityWeight
          (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight),
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖direction‖ ≤ radius → weight / |frequency| ≤ radius →
      contourCentroidFunctional (diskRelabelCurve angular 1 + direction) = contourCentroidFunctional (diskRelabelCurve angular 1) →
      ‖family.canonicalExteriorAffinePhaseField index angular frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskRelabelCurve angular 1 + direction) -
        frequency • diskEulerRotatingField
          (family.canonicalExteriorAffineCoordinate index angular frequency time (diskRelabelCurve angular 1 + direction))‖ ≤
        constant * (weight * ‖direction‖ ^ 2 + weight * ((family.patch index).radius / distance) * ‖direction‖ + weight ^ 2 / |frequency|) := by
  obtain ⟨budgetRadius, budgetPositive, constant, constantOne, budgetBounds⟩ :=
    canonicalExteriorAffineError_exists_uniform_norm_budget
  let threshold := min (1 / 3) (min 1 (2 / (3 * Real.pi)))
  have thresholdPositive : 0 < threshold := by dsimp [threshold]; positivity
  let radius := min budgetRadius (min (1 / 4) (threshold / 2))
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have budgetLe : radius ≤ budgetRadius := min_le_left _ _
  have quarterLe : radius ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have thresholdLe : radius ≤ threshold / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨radius, radiusPositive, constant, constantOne, ?_⟩
  intro count family index angular direction angularSmall angularMember directionMember realValues
    frequency time distance weight nonzero positive weightNonnegative small separated weightBound inside frequencySmall centered
  have actualBudget := budgetBounds family index angular direction (angularSmall.trans budgetLe)
    angularMember directionMember realValues nonzero positive weightNonnegative small separated weightBound
    (inside.trans budgetLe) (frequencySmall.trans budgetLe) centered
  have angularHalf : ‖angular‖ < 1 / 2 := (angularSmall.trans quarterLe).trans_lt (by norm_num)
  have nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < threshold := by
    have baseBound : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ ≤ radius := by linarith [norm_nonneg direction]
    linarith [baseBound.trans thresholdLe]
  have smaller : 8 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
  have identity := family.canonicalExteriorAffinePhaseField_residual_identity index angular angularHalf realValues nearby
    nonzero positive smaller separated (diskRelabelCurve angular 1 + direction)
  dsimp only at identity actualBudget
  simp only [add_sub_cancel_left] at identity
  have displacement : family.relabeledExteriorForcingPrimitive index angular frequency time +
      family.exteriorStrainPhysicalCorrection index angular frequency time direction =
      (diskRelabelCurve angular 1 + direction) -
        family.canonicalExteriorAffineCoordinate index angular frequency time (diskRelabelCurve angular 1 + direction) := by
    unfold canonicalExteriorAffineCoordinate
    generalize baseEq : diskRelabelCurve angular 1 = shape
    generalize primitiveEq : family.relabeledExteriorForcingPrimitive index angular frequency time = primitive
    generalize correctionEq : family.exteriorStrainPhysicalCorrection index angular frequency time = correction
    simp only [add_sub_cancel_left]
    abel
  rw [displacement, smul_sub, smul_sub] at identity
  rw [identity]
  unfold canonicalExteriorHigherContourField at actualBudget ⊢
  generalize sourceEq : family.canonicalProjectedExteriorContourField index time distance positive smaller separated
    (Circle.exp (frequency * time / 2)) = source at actualBudget ⊢
  generalize baseEq : diskRelabelCurve angular 1 = shape at actualBudget ⊢
  generalize correctionEq : family.exteriorStrainPhysicalCorrection index angular frequency time = correction at actualBudget ⊢
  exact (EulerNonuniqueness.General.norm_four_add_sub_le _ _ _ _ _).trans actualBudget

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
