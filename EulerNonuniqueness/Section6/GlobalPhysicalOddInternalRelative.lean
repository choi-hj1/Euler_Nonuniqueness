import EulerNonuniqueness.Section6.PhysicalOddInternalRelative
import EulerNonuniqueness.Section6.GlobalNormalizedOddInternalRelative

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointOddInternalError_global_physical_relative_bound {lower upper minimumPositive : ℝ}
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (upperSmall : upper < 1)
    (minimumPositiveBound : 0 < minimumPositive) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ first second : FourPointConfiguration,
      (fourPointOddPart second).1 ≠ 0 →
      lower ≤ ‖(fourPointOddPart second).2‖ / ‖(fourPointOddPart second).1‖ →
      ‖(fourPointOddPart second).2‖ / ‖(fourPointOddPart second).1‖ ≤ upper →
      minimumPositive * ‖(fourPointOddPart second).1‖ ≤ ‖(fourPointOddPart first).1‖ →
      lower ≤ ‖(fourPointOddPart first).2‖ / ‖(fourPointOddPart first).1‖ →
      ‖(fourPointOddPart first).2‖ / ‖(fourPointOddPart first).1‖ ≤ upper →
      ‖fourPointSignedMoment first‖ + ‖fourPointSignedMoment second‖ <
        radius * ‖(fourPointOddPart second).1‖ →
      ‖fourPointOddInternalError coefficient first - fourPointOddInternalError coefficient second‖ ≤
        bound * |coefficient| /
          (16 * ‖(fourPointOddPart second).1‖ ^ 3) *
          ((‖fourPointSignedMoment first‖ + ‖fourPointSignedMoment second‖) *
              ‖fourPointSignedMoment first - fourPointSignedMoment second‖ +
            (‖centrallySymmetricFourPoint (fourPointOddPart first).1 (fourPointOddPart first).2 -
              centrallySymmetricFourPoint (fourPointOddPart second).1 (fourPointOddPart second).2‖ /
                ‖(fourPointOddPart second).1‖) * ‖fourPointSignedMoment second‖ ^ 2) := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointOddInternalError_global_normalized_relative_bound lowerPositive ordered upperSmall minimumPositiveBound
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient first second scaleNonzero secondLower secondUpper firstMinimum firstLower firstUpper small
  let scale := (fourPointOddPart second).1
  let normalizedFirst := fourPointComplexDilation scale⁻¹ first
  let normalizedSecond := fourPointComplexDilation scale⁻¹ second
  have scalePositive : 0 < ‖scale‖ := norm_pos_iff.mpr scaleNonzero
  have firstOdd : fourPointOddPart normalizedFirst = scale⁻¹ • fourPointOddPart first := fourPointOddPart_dilation _ _
  have secondOdd : fourPointOddPart normalizedSecond = scale⁻¹ • fourPointOddPart second := fourPointOddPart_dilation _ _
  have normalizedPositive : (fourPointOddPart normalizedSecond).1 = 1 := by
    rw [secondOdd]
    change scale⁻¹ * scale = 1
    exact inv_mul_cancel₀ scaleNonzero
  have normalizedNegative : ‖(fourPointOddPart normalizedSecond).2‖ = ‖(fourPointOddPart second).2‖ / ‖scale‖ := by
    rw [secondOdd]
    change ‖scale⁻¹ * (fourPointOddPart second).2‖ = _
    rw [norm_mul, norm_inv]
    ring
  have normalizedFirstNorm : ‖(fourPointOddPart normalizedFirst).1‖ = ‖(fourPointOddPart first).1‖ / ‖scale‖ := by
    rw [firstOdd]
    change ‖scale⁻¹ * (fourPointOddPart first).1‖ = _
    rw [norm_mul, norm_inv]
    ring
  have normalizedFirstRatio : ‖(fourPointOddPart normalizedFirst).2‖ / ‖(fourPointOddPart normalizedFirst).1‖ =
      ‖(fourPointOddPart first).2‖ / ‖(fourPointOddPart first).1‖ := by
    rw [firstOdd]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, norm_mul, norm_inv]
    rw [mul_div_mul_left _ _ (inv_ne_zero (norm_ne_zero_iff.mpr scaleNonzero))]
  have normalizedFirstMinimum : minimumPositive ≤ ‖(fourPointOddPart normalizedFirst).1‖ := by
    rw [normalizedFirstNorm]
    exact (le_div_iff₀ scalePositive).mpr firstMinimum
  have firstNoncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (fourPointOddPart normalizedFirst).1 (fourPointOddPart normalizedFirst).2) := by
    have pNonzero : (fourPointOddPart normalizedFirst).1 ≠ 0 :=
      norm_pos_iff.mp (minimumPositiveBound.trans_le normalizedFirstMinimum)
    have ratioLower : lower ≤ ‖(fourPointOddPart normalizedFirst).2‖ / ‖(fourPointOddPart normalizedFirst).1‖ := by
      rw [normalizedFirstRatio]; exact firstLower
    have ratioUpper : ‖(fourPointOddPart normalizedFirst).2‖ / ‖(fourPointOddPart normalizedFirst).1‖ ≤ upper := by
      rw [normalizedFirstRatio]; exact firstUpper
    apply centrallySymmetricFourPoint_noncollision pNonzero
    · intro zero
      rw [zero, norm_zero, zero_div] at ratioLower
      exact lowerPositive.not_le ratioLower
    · intro zero
      have equal := (sub_eq_zero.mp zero).symm
      rw [equal, div_self (norm_ne_zero_iff.mpr pNonzero)] at ratioUpper
      exact (ratioUpper.trans_lt upperSmall).false
    · intro zero
      have equal : (fourPointOddPart normalizedFirst).2 = -(fourPointOddPart normalizedFirst).1 :=
        eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using zero)
      rw [equal, norm_neg, div_self (norm_ne_zero_iff.mpr pNonzero)] at ratioUpper
      exact (ratioUpper.trans_lt upperSmall).false
  have secondNoncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (fourPointOddPart normalizedSecond).1 (fourPointOddPart normalizedSecond).2) := by
    rw [normalizedPositive]
    exact normalized_central_noncollision
      (lowerPositive.trans_le (by simpa only [normalizedNegative, scale] using secondLower))
      ((by simpa only [normalizedNegative, scale] using secondUpper : ‖(fourPointOddPart normalizedSecond).2‖ ≤ upper).trans_lt upperSmall)
  have momentNorm (positions : FourPointConfiguration) :
      ‖fourPointSignedMoment (fourPointComplexDilation scale⁻¹ positions)‖ = ‖fourPointSignedMoment positions‖ / ‖scale‖ := by
    rw [fourPointSignedMoment_dilation, norm_mul, norm_inv]
    ring
  have momentDifference : ‖fourPointSignedMoment normalizedFirst - fourPointSignedMoment normalizedSecond‖ =
      ‖fourPointSignedMoment first - fourPointSignedMoment second‖ / ‖scale‖ := by
    dsimp only [normalizedFirst, normalizedSecond]
    rw [fourPointSignedMoment_dilation, fourPointSignedMoment_dilation, ← mul_sub, norm_mul, norm_inv]
    ring
  have centralIdentity : centrallySymmetricFourPoint (fourPointOddPart normalizedFirst).1 (fourPointOddPart normalizedFirst).2 -
      centrallySymmetricFourPoint (fourPointOddPart normalizedSecond).1 (fourPointOddPart normalizedSecond).2 =
      fourPointComplexDilation scale⁻¹
        (centrallySymmetricFourPoint (fourPointOddPart first).1 (fourPointOddPart first).2 -
          centrallySymmetricFourPoint (fourPointOddPart second).1 (fourPointOddPart second).2) := by
    rw [firstOdd, secondOdd]
    ext label
    fin_cases label <;> simp [centrallySymmetricFourPoint, fourPointComplexDilation, smul_eq_mul] <;> ring
  have centralNorm : ‖centrallySymmetricFourPoint (fourPointOddPart normalizedFirst).1 (fourPointOddPart normalizedFirst).2 -
      centrallySymmetricFourPoint (fourPointOddPart normalizedSecond).1 (fourPointOddPart normalizedSecond).2‖ =
      ‖centrallySymmetricFourPoint (fourPointOddPart first).1 (fourPointOddPart first).2 -
        centrallySymmetricFourPoint (fourPointOddPart second).1 (fourPointOddPart second).2‖ / ‖scale‖ := by
    rw [centralIdentity, fourPointComplexDilation_norm, norm_inv]
    ring
  have normalizedSmall : ‖fourPointSignedMoment normalizedFirst‖ + ‖fourPointSignedMoment normalizedSecond‖ < radius := by
    rw [momentNorm first, momentNorm second, ← add_div]
    exact (div_lt_iff₀ scalePositive).mpr small
  have normalizedEstimate := estimate 1 normalizedFirst normalizedSecond normalizedPositive normalizedFirstMinimum
    (by rw [normalizedFirstRatio]; exact firstLower) (by rw [normalizedFirstRatio]; exact firstUpper)
    (by simpa only [normalizedNegative, scale] using secondLower)
    (by simpa only [normalizedNegative, scale] using secondUpper) normalizedSmall
  simp only [abs_one, mul_one] at normalizedEstimate
  have actual := mul_le_mul_of_nonneg_left normalizedEstimate (show 0 ≤ |coefficient| / ‖scale‖ by positivity)
  have reconstruct (positions : FourPointConfiguration) :
      fourPointComplexDilation scale (fourPointComplexDilation scale⁻¹ positions) = positions := by
    ext label
    change scale * (scale⁻¹ * positions label) = positions label
    rw [← mul_assoc, mul_inv_cancel₀ scaleNonzero, one_mul]
  rw [momentNorm first, momentNorm second, momentDifference, centralNorm] at actual
  conv_lhs => rw [← reconstruct first, ← reconstruct second]
  rw [
    fourPointOddInternalError_dilation coefficient scaleNonzero normalizedFirst firstNoncollision,
    fourPointOddInternalError_dilation coefficient scaleNonzero normalizedSecond secondNoncollision,
    ← smul_sub, norm_smul, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_star]
  apply actual.trans_eq
  change (|coefficient| / ‖scale‖) * (bound *
      ((‖fourPointSignedMoment first‖ / ‖scale‖ + ‖fourPointSignedMoment second‖ / ‖scale‖) *
        (‖fourPointSignedMoment first - fourPointSignedMoment second‖ / ‖scale‖) +
        (‖centrallySymmetricFourPoint (fourPointOddPart first).1 (fourPointOddPart first).2 -
          centrallySymmetricFourPoint (fourPointOddPart second).1 (fourPointOddPart second).2‖ / ‖scale‖) *
          (‖fourPointSignedMoment second‖ / ‖scale‖) ^ 2) / 16) = _
  field_simp [scalePositive.ne']
  <;> ring

end EulerNonuniqueness.Section6

