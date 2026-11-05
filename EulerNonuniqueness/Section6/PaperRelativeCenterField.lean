import EulerNonuniqueness.Section6.PairedCenterRelativeField
import EulerNonuniqueness.Section6.FourPointCenterProjection
import EulerNonuniqueness.Section6.FourPointInversePowerRelative
import EulerNonuniqueness.Section6.PaperReferenceShapeForcing
import EulerNonuniqueness.Section5.CascadeRelativeFirstMomentHistory

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 6000000

theorem quadrupole_internal_center_field_relative_bound
    {count : ℕ} (scales : Scales) (first second : PatchMotion count) (index : Fin count) (time : ℝ)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {gapFactor radiusFactor : ℝ} (gapPositive : 0 < gapFactor) (radiusNonnegative : 0 ≤ radiusFactor)
    (firstExtent : ∀ patch, ‖patchCentroid first time index patch - quadrupoleCenter first time index‖ ≤
      radiusFactor * scales.length (index.val + 1))
    (secondExtent : ∀ patch, ‖patchCentroid second time index patch - quadrupoleCenter second time index‖ ≤
      radiusFactor * scales.length (index.val + 1))
    (firstSeparated : ∀ positive negative : Fin 4, positive.val < 2 → 2 ≤ negative.val →
      gapFactor * scales.length (index.val + 1) ≤
        ‖patchCentroid first time index positive - patchCentroid first time index negative‖)
    (secondSeparated : ∀ positive negative : Fin 4, positive.val < 2 → 2 ≤ negative.val →
      gapFactor * scales.length (index.val + 1) ≤
        ‖patchCentroid second time index positive - patchCentroid second time index negative‖) :
    ‖fourPointArithmeticCenter (fourPointField
        (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid first time index patch)) -
      fourPointArithmeticCenter (fourPointField
        (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid second time index patch))‖ / scales.location (index.val + 1) ≤
      (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 /
        (gapFactor ^ 2 * scales.location (index.val + 1) ^ 2)) *
          ‖relativeNormalizedFirstMoment scales first second index time‖ +
      (32 * scales.omega (index.val + 1) * radiusFactor / gapFactor ^ 4) *
        (‖centroidAsymmetry second time index‖ / scales.location (index.val + 1)) *
        (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
          (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
            scales.length (index.val + 1)) := by
  let firstPositions : FourPointConfiguration := fun patch => patchCentroid first time index patch
  let secondPositions : FourPointConfiguration := fun patch => patchCentroid second time index patch
  let firstCentered : FourPointConfiguration := fun patch => firstPositions patch - quadrupoleCenter first time index
  let secondCentered : FourPointConfiguration := fun patch => secondPositions patch - quadrupoleCenter second time index
  let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := scales.length_pos (index.val + 1)
  have locationPositive := scales.location_pos (index.val + 1)
  have centeredField (positions : FourPointConfiguration) (center : ℂ) :
      fourPointField coefficient (fun patch => positions patch - center) = fourPointField coefficient positions := by
    simpa only [Pi.add_apply, sub_eq_add_neg] using
      fourPointField_translation_invariant coefficient positions (-center)
  have estimate := fourPointArithmeticCenter_field_relative_signedMoment_bound coefficient firstCentered secondCentered
    (mul_pos gapPositive lengthPositive) (mul_nonneg radiusNonnegative lengthPositive.le)
    firstExtent secondExtent
    (fun positive negative positiveBound negativeBound => by
      simpa only [firstCentered, firstPositions, sub_sub_sub_cancel_right] using
        firstSeparated positive negative positiveBound negativeBound)
    (fun positive negative positiveBound negativeBound => by
      simpa only [secondCentered, secondPositions, sub_sub_sub_cancel_right] using
        secondSeparated positive negative positiveBound negativeBound)
  rw [centeredField firstPositions, centeredField secondPositions,
    fourPointSignedMoment_centered firstPositions, fourPointSignedMoment_centered secondPositions] at estimate
  have firstMoment := centroid_fourPointSignedMoment first time index
  have secondMoment := centroid_fourPointSignedMoment second time index
  change fourPointSignedMoment firstPositions = 4 * centroidAsymmetry first time index at firstMoment
  change fourPointSignedMoment secondPositions = 4 * centroidAsymmetry second time index at secondMoment
  rw [firstMoment, secondMoment, ← mul_sub, norm_mul, norm_mul] at estimate
  norm_num only [Complex.norm_ofNat] at estimate
  have coefficientPositive : 0 < coefficient := by dsimp only [coefficient]; positivity
  rw [abs_of_pos coefficientPositive] at estimate
  have normalizedMoment : ‖relativeNormalizedFirstMoment scales first second index time‖ =
      (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) *
        ‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ := by
    rw [relativeNormalizedFirstMoment, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  apply (div_le_div_of_nonneg_right estimate locationPositive.le).trans_eq
  rw [normalizedMoment]
  dsimp only [coefficient, firstCentered, secondCentered, firstPositions, secondPositions]
  field_simp
  <;> ring

end EulerNonuniqueness.Paper
