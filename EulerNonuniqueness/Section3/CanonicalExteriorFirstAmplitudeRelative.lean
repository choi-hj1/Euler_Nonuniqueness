import EulerNonuniqueness.Section3.CanonicalExteriorAffineParameter
import EulerNonuniqueness.Section3.CanonicalPhysicalAmplitudeBound
import EulerNonuniqueness.Section3.RelabeledPrimitiveSeriesDifference
import EulerNonuniqueness.General.AffineResidualRelativeRemainder

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

theorem canonicalExteriorFirstAmplitudeError_exists_relative_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (firstAngular finalAngular : PeriodicC1HolderHalf),
      ∀ (firstSmall : ‖firstAngular‖ < 1 / 2) (finalSmall : ‖finalAngular‖ < 1 / 2),
      ‖firstAngular‖ ≤ radius → ‖finalAngular‖ ≤ radius →
      (∀ label, star (firstAngular.val.1 label) = firstAngular.val.1 label) →
      (∀ label, star (finalAngular.val.1 label) = finalAngular.val.1 label) →
      ‖diskRelabelCurve firstAngular 1‖ ≤ 3 → ‖diskRelabelCurve finalAngular 1‖ ≤ 3 →
      ∀ {frequency time : ℝ}, frequency ≠ 0 →
      Summable (fun degree => (24 : ℝ) ^ (degree + 1) *
        ‖family.exteriorMaterialCoefficientDerivative index degree time‖) →
      ∀ firstData finalData : PeriodicC1HolderHalf,
      ‖(fixedRelabelEquivalence firstAngular firstSmall
          (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
        family.exteriorStrainAmplitudeCorrection index firstAngular frequency time
          (firstData - diskRelabelCurve firstAngular 1)) -
        (fixedRelabelEquivalence finalAngular finalSmall
          (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
        family.exteriorStrainAmplitudeCorrection index finalAngular frequency time
          (finalData - diskRelabelCurve finalAngular 1))‖ ≤
      constant * ((∑' degree, (24 : ℝ) ^ (degree + 1) *
        ‖family.exteriorMaterialCoefficientDerivative index degree time‖) / |frequency|) *
        (‖firstData - finalData‖ +
          (1 + ‖finalData - diskRelabelCurve finalAngular 1‖) * ‖firstAngular - finalAngular‖) := by
  obtain ⟨correctionRadius, correctionPositive, correctionConstant, correctionOne, correctionBound, correctionDifference⟩ :=
    movingStrainRealCorrectionCLM_exists_uniform_relabel_bounds
  obtain ⟨baseRadius, basePositive, baseConstant, _, baseDifference⟩ := diskRelabelMap_exists_uniform_lipschitz
  let constant := 2 * (baseConstant : ℝ) + correctionConstant * (1 + baseConstant) + 1
  have correctionNonnegative : 0 ≤ correctionConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have productNonnegative : 0 ≤ correctionConstant * (1 + (baseConstant : ℝ)) := by positivity
    dsimp [constant]
    linarith [baseConstant.coe_nonneg]
  refine ⟨min correctionRadius baseRadius, lt_min correctionPositive basePositive, constant, constantOne, ?_⟩
  intro count family index firstAngular finalAngular firstSmall finalSmall firstInside finalInside firstReal finalReal
    firstBound finalBound frequency time nonzero weighted firstData finalData
  let budget := ∑' degree, (24 : ℝ) ^ (degree + 1) * ‖family.exteriorMaterialCoefficientDerivative index degree time‖
  have budgetNonnegative : 0 ≤ budget := tsum_nonneg (fun degree => by positivity)
  have weightedTwo : Summable (fun degree => (2 : ℝ) ^ (degree + 1) *
      ‖family.exteriorMaterialCoefficientDerivative index degree time‖) :=
    Summable.of_nonneg_of_le (fun degree => by positivity) (fun degree => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 24) _) (norm_nonneg _)) weighted
  have primitive := relabeledForcingPrimitiveSeries_difference_bound firstAngular finalAngular firstSmall finalSmall
    firstReal finalReal firstBound finalBound nonzero (family.exteriorMaterialCoefficientDerivative index) time weighted
  rw [← relabeledForcingPrimitiveSeries_fixedRelabel firstAngular firstSmall firstReal nonzero _ time weightedTwo,
    ← relabeledForcingPrimitiveSeries_fixedRelabel finalAngular finalSmall finalReal nonzero _ time weightedTwo] at primitive
  have base := baseDifference firstAngular finalAngular
    (firstInside.trans (min_le_right _ _)) (finalInside.trans (min_le_right _ _))
  have single := weighted.le_tsum 0 (fun degree _ => by positivity)
  norm_num only [zero_add, pow_one] at single
  have singleBound : ‖diskForcingPhase 0 frequency time * family.exteriorMaterialCoefficientDerivative index 0 time‖ ≤ budget := by
    rw [norm_mul, diskForcingPhase_norm, one_mul]
    change 24 * ‖family.exteriorMaterialCoefficientDerivative index 0 time‖ ≤ budget at single
    linarith [norm_nonneg (family.exteriorMaterialCoefficientDerivative index 0 time)]
  have correctionScale := (correctionBound firstAngular (firstInside.trans (min_le_left _ _)) _).trans
    (mul_le_mul_of_nonneg_left singleBound correctionNonnegative)
  have correctionPair := (correctionDifference firstAngular finalAngular
    (firstInside.trans (min_le_left _ _)) (finalInside.trans (min_le_left _ _)) _).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left singleBound correctionNonnegative)
      (norm_nonneg (firstAngular - finalAngular)))
  have scaledBound : ‖family.exteriorStrainAmplitudeCorrection index firstAngular frequency time‖ ≤
      correctionConstant * (budget / |frequency|) := by
    rw [exteriorStrainAmplitudeCorrection, norm_smul, Real.norm_eq_abs, abs_inv]
    exact (mul_le_mul_of_nonneg_left correctionScale (by positivity)).trans_eq (by ring)
  have scaledPair : ‖family.exteriorStrainAmplitudeCorrection index firstAngular frequency time -
      family.exteriorStrainAmplitudeCorrection index finalAngular frequency time‖ ≤
      correctionConstant * (budget / |frequency|) * ‖firstAngular - finalAngular‖ := by
    rw [exteriorStrainAmplitudeCorrection, exteriorStrainAmplitudeCorrection, ← smul_sub,
      norm_smul, Real.norm_eq_abs, abs_inv]
    exact (mul_le_mul_of_nonneg_left correctionPair (by positivity)).trans_eq (by ring)
  have defectDifference : ‖(firstData - diskRelabelCurve firstAngular 1) -
      (finalData - diskRelabelCurve finalAngular 1)‖ ≤
      ‖firstData - finalData‖ + (baseConstant : ℝ) * ‖firstAngular - finalAngular‖ := by
    have identity : (firstData - diskRelabelCurve firstAngular 1) - (finalData - diskRelabelCurve finalAngular 1) =
        (firstData - finalData) - (diskRelabelCurve firstAngular 1 - diskRelabelCurve finalAngular 1) := by abel
    rw [identity]
    exact (norm_sub_le _ _).trans (add_le_add_left base _)
  have applied := EulerNonuniqueness.General.norm_operator_apply_difference_le
    (family.exteriorStrainAmplitudeCorrection index firstAngular frequency time)
    (family.exteriorStrainAmplitudeCorrection index finalAngular frequency time)
    (firstData - diskRelabelCurve firstAngular 1) (finalData - diskRelabelCurve finalAngular 1)
  have appliedBound := applied.trans (add_le_add
    (mul_le_mul scaledBound defectDifference (norm_nonneg _) (by positivity))
    (mul_le_mul_of_nonneg_right scaledPair (norm_nonneg _)))
  have primitiveBound := primitive.trans (mul_le_mul_of_nonneg_left base (by positivity : 0 ≤ (2 / |frequency|) * budget))
  have triangle := norm_add_le
    (fixedRelabelEquivalence firstAngular firstSmall (family.exteriorAmplitudeDerivativePrimitive index frequency time) -
      fixedRelabelEquivalence finalAngular finalSmall (family.exteriorAmplitudeDerivativePrimitive index frequency time))
    (family.exteriorStrainAmplitudeCorrection index firstAngular frequency time (firstData - diskRelabelCurve firstAngular 1) -
      family.exteriorStrainAmplitudeCorrection index finalAngular frequency time (finalData - diskRelabelCurve finalAngular 1))
  have identity :
      (fixedRelabelEquivalence firstAngular firstSmall (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
        family.exteriorStrainAmplitudeCorrection index firstAngular frequency time (firstData - diskRelabelCurve firstAngular 1)) -
      (fixedRelabelEquivalence finalAngular finalSmall (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
        family.exteriorStrainAmplitudeCorrection index finalAngular frequency time (finalData - diskRelabelCurve finalAngular 1)) =
      (fixedRelabelEquivalence firstAngular firstSmall (family.exteriorAmplitudeDerivativePrimitive index frequency time) -
        fixedRelabelEquivalence finalAngular finalSmall (family.exteriorAmplitudeDerivativePrimitive index frequency time)) +
      (family.exteriorStrainAmplitudeCorrection index firstAngular frequency time (firstData - diskRelabelCurve firstAngular 1) -
        family.exteriorStrainAmplitudeCorrection index finalAngular frequency time (finalData - diskRelabelCurve finalAngular 1)) := by abel
  rw [identity]
  apply triangle.trans
  apply (add_le_add primitiveBound appliedBound).trans
  have firstLarge : correctionConstant ≤ constant := by dsimp [constant]; nlinarith [baseConstant.coe_nonneg]
  have finalLarge : 2 * (baseConstant : ℝ) + correctionConstant * baseConstant + correctionConstant ≤ constant := by
    dsimp [constant]
    linarith
  have scalar := add_le_add
    (mul_le_mul_of_nonneg_right firstLarge (mul_nonneg (by positivity : 0 ≤ budget / |frequency|) (norm_nonneg (firstData - finalData))))
    (mul_le_mul_of_nonneg_right finalLarge (mul_nonneg (by positivity : 0 ≤ budget / |frequency|)
      (mul_nonneg (by positivity : 0 ≤ 1 + ‖finalData - diskRelabelCurve finalAngular 1‖) (norm_nonneg (firstAngular - finalAngular)))))
  have nonnegative : 0 ≤ (2 * (baseConstant : ℝ) + correctionConstant * baseConstant) *
      (budget / |frequency|) * ‖finalData - diskRelabelCurve finalAngular 1‖ * ‖firstAngular - finalAngular‖ := by positivity
  have correctionTermNonnegative : 0 ≤ correctionConstant * (budget / |frequency|) *
      ‖firstAngular - finalAngular‖ := by positivity
  have enlarged :
      (2 / |frequency| * budget) * ((baseConstant : ℝ) * ‖firstAngular - finalAngular‖) +
        (correctionConstant * (budget / |frequency|) *
          (‖firstData - finalData‖ + (baseConstant : ℝ) * ‖firstAngular - finalAngular‖) +
          correctionConstant * (budget / |frequency|) * ‖firstAngular - finalAngular‖ *
            ‖finalData - diskRelabelCurve finalAngular 1‖) ≤
      correctionConstant * ((budget / |frequency|) * ‖firstData - finalData‖) +
        (2 * (baseConstant : ℝ) + correctionConstant * baseConstant + correctionConstant) *
          ((budget / |frequency|) * ((1 + ‖finalData - diskRelabelCurve finalAngular 1‖) *
            ‖firstAngular - finalAngular‖)) := by
    apply sub_nonneg.mp
    convert add_nonneg correctionTermNonnegative nonnegative using 1 <;> ring
  apply enlarged.trans
  convert scalar using 1 <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
