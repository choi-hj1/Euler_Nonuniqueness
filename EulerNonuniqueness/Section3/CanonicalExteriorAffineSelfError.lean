import EulerNonuniqueness.Section3.CanonicalExteriorAffineShift
import EulerNonuniqueness.Section3.DiskRotatingUniformDifference

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorAffineCoordinate_exists_uniform_self_error :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular direction : PeriodicC1HolderHalf), ‖angular‖ ≤ radius →
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      4 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖direction‖ ≤ radius → weight / |frequency| ≤ radius →
      let data := diskRelabelCurve angular 1 + direction
      let shifted := family.canonicalExteriorAffineCoordinate index angular frequency time data
      ‖frequency • diskEulerRotatingField data -
        frequency • (fderiv ℝ diskEulerRotatingField data (data - shifted)) -
        frequency • diskEulerRotatingField shifted‖ ≤ constant * weight ^ 2 / |frequency| := by
  obtain ⟨selfRadius, selfPositive, selfConstant, selfOne, selfBounds⟩ :=
    diskEulerRotatingField_exists_uniform_shifted_self_error
  obtain ⟨shiftRadius, shiftPositive, shiftBounds⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_shift_admissibility selfRadius selfPositive
  obtain ⟨nearRadius, nearPositive, nearConstant, nearOne, nearBounds⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_near_identity_bound
  let radius := min shiftRadius (min nearRadius 1)
  let constant := 4 * selfConstant * nearConstant ^ 2 + 1
  have selfNonnegative : 0 ≤ selfConstant := by linarith
  have nearNonnegative : 0 ≤ nearConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 4 * selfConstant * nearConstant ^ 2 := by positivity
    dsimp [constant]
    linarith
  have shiftLe : radius ≤ shiftRadius := min_le_left _ _
  have nearLe : radius ≤ nearRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusOne : radius ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_⟩
  intro count family index angular direction angularSmall realValues frequency time distance weight
    nonzero positive weightNonnegative small separated weightBound inside frequencySmall
  have admissible := shiftBounds family index angular direction (angularSmall.trans shiftLe) realValues
    nonzero positive weightNonnegative small separated weightBound (inside.trans shiftLe) (frequencySmall.trans shiftLe)
  have nearEstimate := nearBounds family index angular (angularSmall.trans nearLe) realValues nonzero positive
    weightNonnegative small separated weightBound (diskRelabelCurve angular 1 + direction)
  simp only [add_sub_cancel_left] at nearEstimate
  have directionBound : ‖direction‖ ≤ 1 := by
    linarith [norm_nonneg (diskRelabelCurve angular 1 - standardCircleBanach)]
  have correctionBound :
      ‖(diskRelabelCurve angular 1 + direction) -
        family.canonicalExteriorAffineCoordinate index angular frequency time (diskRelabelCurve angular 1 + direction)‖ ≤
      2 * nearConstant * (weight / |frequency|) := by
    rw [norm_sub_rev]
    exact nearEstimate.trans (by
      have numerical := mul_le_mul_of_nonneg_left (by linarith : 1 + ‖direction‖ ≤ 2)
        (show 0 ≤ nearConstant * (weight / |frequency|) by positivity)
      convert numerical using 1 <;> ring)
  dsimp only
  generalize baseEq : diskRelabelCurve angular 1 + direction = data at *
  generalize shiftedEq : family.canonicalExteriorAffineCoordinate index angular frequency time data = shifted at *
  have actual := selfBounds data (data - shifted) frequency admissible
  rw [sub_sub_cancel] at actual
  have squared := pow_le_pow_left₀ (norm_nonneg (data - shifted)) correctionBound 2
  have scaled := mul_le_mul_of_nonneg_left squared (mul_nonneg (abs_nonneg frequency) selfNonnegative)
  have frequencyPositive : 0 < |frequency| := abs_pos.mpr nonzero
  have scalarIdentity (modulus : ℝ) (modulusPositive : 0 < modulus) :
      modulus * selfConstant * (2 * nearConstant * (weight / modulus)) ^ 2 =
      (4 * selfConstant * nearConstant ^ 2) * (weight ^ 2 / modulus) := by
    field_simp [modulusPositive.ne']
    <;> ring
  have coefficientLe : 4 * selfConstant * nearConstant ^ 2 ≤ constant := by dsimp [constant]; linarith
  exact actual.trans (scaled.trans (by
    rw [scalarIdentity |frequency| frequencyPositive]
    have numerical := mul_le_mul_of_nonneg_right coefficientLe (div_nonneg (sq_nonneg weight) frequencyPositive.le)
    simpa only [div_eq_mul_inv, mul_assoc] using numerical))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
