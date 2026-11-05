import EulerNonuniqueness.Section6.PairedDiagonalInternalRate
import EulerNonuniqueness.Section6.PaperRelativeCenterField

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def quadrupoleInternalDilationRate {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℝ :=
  fourPointCenteredDilationRate (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
    (fun patch => patchCentroid motion time index patch)

theorem quadrupole_internal_dilation_rate_relative_bound
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
    |quadrupoleInternalDilationRate scales first index time - quadrupoleInternalDilationRate scales second index time| /
        scales.length (index.val + 1) ^ 2 ≤
      (4 * scales.omega (index.val + 1) / (gapFactor ^ 2 * scales.location (index.val + 1))) *
        (‖centroidAsymmetry first time index‖ + ‖centroidAsymmetry second time index‖) *
          ‖relativeNormalizedFirstMoment scales first second index time‖ +
      (128 * scales.omega (index.val + 1) * radiusFactor / gapFactor ^ 4) *
        (‖centroidAsymmetry first time index‖ * ‖centroidAsymmetry second time index‖ /
          scales.length (index.val + 1) ^ 2) *
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
  have centeredRate (positions : FourPointConfiguration) (center : ℂ) :
      fourPointCenteredDilationRate coefficient (fun patch => positions patch - center) =
        fourPointCenteredDilationRate coefficient positions := by
    have field := fourPointField_translation_invariant coefficient positions (-center)
    have field' : fourPointField coefficient (fun patch => positions patch - center) =
        fourPointField coefficient positions := by simpa only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg] using field
    rw [fourPointCenteredDilationRate, field', fourPointSignedMoment_centered]
    rfl
  have estimate := fourPointCenteredDilationRate_relative_signedMoment_bound coefficient firstCentered secondCentered
    (mul_pos gapPositive lengthPositive) (mul_nonneg radiusNonnegative lengthPositive.le) firstExtent secondExtent
    (fun positive negative positiveBound negativeBound => by
      simpa only [firstCentered, firstPositions, sub_sub_sub_cancel_right] using
        firstSeparated positive negative positiveBound negativeBound)
    (fun positive negative positiveBound negativeBound => by
      simpa only [secondCentered, secondPositions, sub_sub_sub_cancel_right] using
        secondSeparated positive negative positiveBound negativeBound)
  rw [centeredRate firstPositions, centeredRate secondPositions,
    fourPointSignedMoment_centered firstPositions, fourPointSignedMoment_centered secondPositions] at estimate
  have firstMoment := centroid_fourPointSignedMoment first time index
  have secondMoment := centroid_fourPointSignedMoment second time index
  change fourPointSignedMoment firstPositions = 4 * centroidAsymmetry first time index at firstMoment
  change fourPointSignedMoment secondPositions = 4 * centroidAsymmetry second time index at secondMoment
  rw [firstMoment, secondMoment, ← mul_sub, norm_mul, norm_mul, norm_mul] at estimate
  norm_num only [Complex.norm_ofNat] at estimate
  have coefficientPositive : 0 < coefficient := by dsimp only [coefficient]; positivity
  rw [abs_of_pos coefficientPositive] at estimate
  have normalizedMoment : ‖relativeNormalizedFirstMoment scales first second index time‖ =
      (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) *
        ‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ := by
    rw [relativeNormalizedFirstMoment, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  apply (div_le_div_of_nonneg_right estimate (sq_nonneg (scales.length (index.val + 1)))).trans_eq
  rw [normalizedMoment]
  dsimp only [quadrupoleInternalDilationRate, coefficient, firstCentered, secondCentered, firstPositions, secondPositions]
  field_simp
  <;> ring

end EulerNonuniqueness.Paper
