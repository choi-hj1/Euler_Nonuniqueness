import EulerNonuniqueness.Section6.CompactNormalizedInternalBound

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointShape_uniform_physical_annular_internal_bound {lower upper : ℝ}
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (upperSmall : upper < 1) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ positions : FourPointConfiguration,
      (fourPointOddPart positions).1 ≠ 0 →
      lower ≤ ‖(fourPointOddPart positions).2‖ / ‖(fourPointOddPart positions).1‖ →
      ‖(fourPointOddPart positions).2‖ / ‖(fourPointOddPart positions).1‖ ≤ upper →
      ‖fourPointSignedMoment positions‖ < radius * ‖(fourPointOddPart positions).1‖ →
      ‖pointShapeForcing (fourPointOddPart positions).1 (fourPointOddPart positions).2
          (fourPointOddInternalError coefficient positions).1 (fourPointOddInternalError coefficient positions).2‖ ≤
        bound * |coefficient| * ‖fourPointSignedMoment positions‖ ^ 2 /
          (16 * ‖(fourPointOddPart positions).1‖ ^ 4) := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointShape_uniform_annular_internal_bound lowerPositive ordered upperSmall
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient positions positiveNonzero negativeLower negativeUpper momentSmall
  let scale := (fourPointOddPart positions).1
  let normalized := fourPointComplexDilation scale⁻¹ positions
  have scaleNonzero : scale ≠ 0 := positiveNonzero
  have scalePositive : 0 < ‖scale‖ := norm_pos_iff.mpr scaleNonzero
  have normalizedOdd : fourPointOddPart normalized = scale⁻¹ • fourPointOddPart positions :=
    fourPointOddPart_dilation _ _
  have normalizedPositive : (fourPointOddPart normalized).1 = 1 := by
    rw [normalizedOdd]
    change scale⁻¹ * scale = 1
    exact inv_mul_cancel₀ scaleNonzero
  have normalizedNegative : ‖(fourPointOddPart normalized).2‖ =
      ‖(fourPointOddPart positions).2‖ / ‖scale‖ := by
    rw [normalizedOdd]
    change ‖scale⁻¹ * (fourPointOddPart positions).2‖ = _
    rw [norm_mul, norm_inv]
    ring
  have normalizedMoment : ‖fourPointSignedMoment normalized‖ =
      ‖fourPointSignedMoment positions‖ / ‖scale‖ := by
    rw [fourPointSignedMoment_dilation, norm_mul, norm_inv]
    ring
  have reconstruct : fourPointComplexDilation scale normalized = positions := by
    funext label
    change scale * (scale⁻¹ * positions label) = positions label
    rw [← mul_assoc, mul_inv_cancel₀ scaleNonzero, one_mul]
  have actual := estimate coefficient scale normalized scaleNonzero normalizedPositive
    (by simpa only [normalizedNegative, scale] using negativeLower)
    (by simpa only [normalizedNegative, scale] using negativeUpper)
    (by rw [normalizedMoment]; exact (div_lt_iff₀ scalePositive).mpr momentSmall)
  rw [reconstruct] at actual
  exact actual

end EulerNonuniqueness.Section6
