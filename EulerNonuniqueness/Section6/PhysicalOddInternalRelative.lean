import EulerNonuniqueness.Section6.NormalizedOddInternalRelative

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointComplexDilation_norm (scale : ℂ) (positions : FourPointConfiguration) :
    ‖fourPointComplexDilation scale positions‖ = ‖scale‖ * ‖positions‖ := by
  change ‖scale • positions‖ = _
  exact norm_smul _ _

theorem fourPointOddInternalError_uniform_physical_relative_bound {lower upper : ℝ}
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (upperSmall : upper < 1) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ first second : FourPointConfiguration,
      (fourPointOddPart second).1 ≠ 0 →
      lower ≤ ‖(fourPointOddPart second).2‖ / ‖(fourPointOddPart second).1‖ →
      ‖(fourPointOddPart second).2‖ / ‖(fourPointOddPart second).1‖ ≤ upper →
      FourPointNoncollision (centrallySymmetricFourPoint (fourPointOddPart first).1 (fourPointOddPart first).2) →
      ‖centrallySymmetricFourPoint (fourPointOddPart first).1 (fourPointOddPart first).2 -
          centrallySymmetricFourPoint (fourPointOddPart second).1 (fourPointOddPart second).2‖ +
        (‖fourPointSignedMoment first‖ + ‖fourPointSignedMoment second‖) / 4 ≤
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
    fourPointOddInternalError_normalized_relative_bound lowerPositive ordered upperSmall
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient first second scaleNonzero secondLower secondUpper firstNoncollision small
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
  have normalizedCollision : FourPointNoncollision (centrallySymmetricFourPoint
      (fourPointOddPart normalizedFirst).1 (fourPointOddPart normalizedFirst).2) := by
    rw [firstOdd]
    change FourPointNoncollision (centrallySymmetricFourPoint
      (scale⁻¹ * (fourPointOddPart first).1) (scale⁻¹ * (fourPointOddPart first).2))
    rw [centrallySymmetricFourPoint_dilation]
    exact firstNoncollision.dilation (inv_ne_zero scaleNonzero)
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
  have normalizedSmall : ‖centrallySymmetricFourPoint (fourPointOddPart normalizedFirst).1 (fourPointOddPart normalizedFirst).2 -
      centrallySymmetricFourPoint (fourPointOddPart normalizedSecond).1 (fourPointOddPart normalizedSecond).2‖ +
      (‖fourPointSignedMoment normalizedFirst‖ + ‖fourPointSignedMoment normalizedSecond‖) / 4 ≤ radius := by
    rw [centralNorm, momentNorm first, momentNorm second]
    have actual := (div_le_iff₀ scalePositive).mpr small
    convert actual using 1 <;> ring
  have actual := estimate coefficient scale normalizedFirst normalizedSecond scaleNonzero normalizedPositive
    (by simpa only [normalizedNegative, scale] using secondLower)
    (by simpa only [normalizedNegative, scale] using secondUpper) normalizedCollision normalizedSmall
  have reconstruct (positions : FourPointConfiguration) :
      fourPointComplexDilation scale (fourPointComplexDilation scale⁻¹ positions) = positions := by
    ext label
    change scale * (scale⁻¹ * positions label) = positions label
    rw [← mul_assoc, mul_inv_cancel₀ scaleNonzero, one_mul]
  rw [reconstruct first, reconstruct second, momentNorm first, momentNorm second, momentDifference, centralNorm] at actual
  apply actual.trans_eq
  change bound * |coefficient| / ‖scale‖ *
      ((‖fourPointSignedMoment first‖ / ‖scale‖ + ‖fourPointSignedMoment second‖ / ‖scale‖) *
        (‖fourPointSignedMoment first - fourPointSignedMoment second‖ / ‖scale‖) +
        (‖centrallySymmetricFourPoint (fourPointOddPart first).1 (fourPointOddPart first).2 -
          centrallySymmetricFourPoint (fourPointOddPart second).1 (fourPointOddPart second).2‖ / ‖scale‖) *
          (‖fourPointSignedMoment second‖ / ‖scale‖) ^ 2) / 16 = _
  field_simp [scalePositive.ne']
  <;> ring

end EulerNonuniqueness.Section6
