import EulerNonuniqueness.Section3.CanonicalExteriorCommonShiftRelative
import EulerNonuniqueness.Section3.DiskNormalizedSpectralRelativeIncrement

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

open EulerNonuniqueness.Section6

def canonicalExteriorCommonNormalizedCoordinate {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time : ℝ)
    (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskNormalizedSpectralCoordinate (family.canonicalExteriorAffineCoordinate index angular frequency time data)

theorem canonicalExteriorCommonNormalizedCoordinate_exists_relative_shift_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (firstAngular finalAngular firstData finalData : PeriodicC1HolderHalf),
      ‖firstAngular‖ ≤ radius → ‖finalAngular‖ ≤ radius →
      (∀ label, star (firstAngular.val.1 label) = firstAngular.val.1 label) →
      (∀ label, star (finalAngular.val.1 label) = finalAngular.val.1 label) →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      48 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      let firstShift := firstData - family.canonicalExteriorAffineCoordinate index firstAngular frequency time firstData
      let finalShift := finalData - family.canonicalExteriorAffineCoordinate index finalAngular frequency time finalData
      ‖firstData - standardCircleBanach‖ + (‖firstShift‖ + ‖finalShift‖) ≤ radius →
      ‖finalData - standardCircleBanach‖ + (‖firstShift‖ + ‖finalShift‖) ≤ radius →
      ‖finalData - diskRelabelCurve finalAngular 1‖ ≤ 1 →
      ‖(family.canonicalExteriorCommonNormalizedCoordinate index firstAngular frequency time firstData -
          diskNormalizedSpectralCoordinate firstData) -
        (family.canonicalExteriorCommonNormalizedCoordinate index finalAngular frequency time finalData -
          diskNormalizedSpectralCoordinate finalData)‖ ≤
      constant * (weight / |frequency|) * (‖firstData - finalData‖ + ‖firstAngular - finalAngular‖) := by
  obtain ⟨shiftRadius, shiftPositive, shiftConstant, shiftOne, shifts⟩ :=
    canonicalExteriorAffineCoordinate_exists_common_shift_relative
  obtain ⟨absoluteRadius, absolutePositive, absoluteConstant, absoluteOne, absolute⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_near_identity_bound
  obtain ⟨normalRadius, normalPositive, normalConstant, normalNonnegative, normal⟩ :=
    diskNormalizedSpectralCoordinate_exists_relative_shift_ball
  let radius := min shiftRadius (min absoluteRadius normalRadius)
  let constant := 2 * normalConstant * (shiftConstant + absoluteConstant) + 1
  have shiftNonnegative : 0 ≤ shiftConstant := le_trans (by norm_num) shiftOne
  have absoluteNonnegative : 0 ≤ absoluteConstant := le_trans (by norm_num) absoluteOne
  have constantOne : 1 ≤ constant := by
    have productNonnegative := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) normalNonnegative)
      (add_nonneg shiftNonnegative absoluteNonnegative)
    dsimp [constant]
    linarith
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_⟩
  intro count family index firstAngular finalAngular firstData finalData firstInside finalInside firstReal finalReal
    frequency time distance weight nonzero positive weightNonnegative small separated weightBound
    firstShift finalShift firstJoint finalJoint finalDefect
  have shift := shifts family index firstAngular finalAngular
    (firstInside.trans (min_le_left _ _)) (finalInside.trans (min_le_left _ _)) firstReal finalReal
    nonzero positive weightNonnegative small separated weightBound firstData finalData
  have finalAbsolute := absolute family index finalAngular
    (finalInside.trans ((min_le_right _ _).trans (min_le_left _ _))) finalReal nonzero positive weightNonnegative
    (by linarith [(family.patch index).radius_positive]) separated weightBound finalData
  rw [norm_sub_rev] at finalAbsolute
  have normalActual := normal firstData finalData firstShift finalShift
    (firstJoint.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (finalJoint.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have firstReconstruct : firstData - firstShift =
      family.canonicalExteriorAffineCoordinate index firstAngular frequency time firstData := by
    dsimp only [firstShift]
    abel
  have finalReconstruct : finalData - finalShift =
      family.canonicalExteriorAffineCoordinate index finalAngular frequency time finalData := by
    dsimp only [finalShift]
    abel
  rw [firstReconstruct, finalReconstruct] at normalActual
  change ‖(family.canonicalExteriorCommonNormalizedCoordinate index firstAngular frequency time firstData -
      diskNormalizedSpectralCoordinate firstData) -
    (family.canonicalExteriorCommonNormalizedCoordinate index finalAngular frequency time finalData -
      diskNormalizedSpectralCoordinate finalData)‖ ≤ _ at normalActual
  have factorNonnegative : 0 ≤ weight / |frequency| := by positivity
  have shiftSimplified : ‖firstShift - finalShift‖ ≤
      shiftConstant * (weight / |frequency|) * (‖firstData - finalData‖ + 2 * ‖firstAngular - finalAngular‖) := by
    apply shift.trans
    gcongr
    linarith
  have absoluteSimplified : ‖finalShift‖ ≤ 2 * absoluteConstant * (weight / |frequency|) := by
    apply finalAbsolute.trans
    have numerical := mul_le_mul_of_nonneg_left (by linarith : 1 + ‖finalData - diskRelabelCurve finalAngular 1‖ ≤ 2)
      (mul_nonneg absoluteNonnegative factorNonnegative)
    exact numerical.trans_eq (by ring)
  have estimate := add_le_add shiftSimplified
    (mul_le_mul_of_nonneg_left absoluteSimplified (norm_nonneg (firstData - finalData)))
  apply normalActual.trans
  apply (mul_le_mul_of_nonneg_left estimate normalNonnegative).trans
  have firstLarge : normalConstant * (shiftConstant + 2 * absoluteConstant) ≤ constant := by
    dsimp [constant]
    nlinarith
  have finalLarge : normalConstant * (2 * shiftConstant) ≤ constant := by
    dsimp [constant]
    nlinarith
  have numerical := add_le_add
    (mul_le_mul_of_nonneg_right firstLarge (mul_nonneg factorNonnegative (norm_nonneg (firstData - finalData))))
    (mul_le_mul_of_nonneg_right finalLarge (mul_nonneg factorNonnegative (norm_nonneg (firstAngular - finalAngular))))
  convert numerical using 1 <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
