import EulerNonuniqueness.Section6.UniformOddInternalRelative

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointOddInternalError_balanced (coefficient : ℝ) (positions : FourPointConfiguration) :
    fourPointOddInternalError coefficient positions =
      fourPointOddInternalError coefficient
        (centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 +
          fourPointPairCenterMode (fourPointSignedMoment positions / 4) (-(fourPointSignedMoment positions / 4))) := by
  have fields : fourPointField coefficient positions =
      fourPointField coefficient
        (centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 +
          fourPointPairCenterMode (fourPointSignedMoment positions / 4) (-(fourPointSignedMoment positions / 4))) := by
    have center : ((positions 0 + positions 1) / 2 - (positions 2 + positions 3) / 2) / 2 =
        fourPointSignedMoment positions / 4 := by
      rw [fourPointSignedMoment_centerDifference]
      ring
    conv_lhs => rw [fourPoint_increment_decomposition positions]
    rw [fourPointField_pairCenter_translation, center]
    rfl
  have odd : fourPointOddPart
      (centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 +
        fourPointPairCenterMode (fourPointSignedMoment positions / 4) (-(fourPointSignedMoment positions / 4))) =
      fourPointOddPart positions := by
    ext <;> simp [fourPointOddPart, centrallySymmetricFourPoint, fourPointPairCenterMode] <;> ring
  simp only [fourPointOddInternalError, fields, odd]

theorem fourPointOddInternalError_normalized_relative_bound {lower upper : ℝ}
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (upperSmall : upper < 1) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ, ∀ scale : ℂ,
      ∀ first second : FourPointConfiguration, scale ≠ 0 →
      (fourPointOddPart second).1 = 1 →
      lower ≤ ‖(fourPointOddPart second).2‖ → ‖(fourPointOddPart second).2‖ ≤ upper →
      FourPointNoncollision (centrallySymmetricFourPoint (fourPointOddPart first).1 (fourPointOddPart first).2) →
      ‖centrallySymmetricFourPoint (fourPointOddPart first).1 (fourPointOddPart first).2 -
          centrallySymmetricFourPoint (fourPointOddPart second).1 (fourPointOddPart second).2‖ +
        (‖fourPointSignedMoment first‖ + ‖fourPointSignedMoment second‖) / 4 ≤ radius →
      ‖fourPointOddInternalError coefficient (fourPointComplexDilation scale first) -
        fourPointOddInternalError coefficient (fourPointComplexDilation scale second)‖ ≤
        bound * |coefficient| / ‖scale‖ *
          ((‖fourPointSignedMoment first‖ + ‖fourPointSignedMoment second‖) *
              ‖fourPointSignedMoment first - fourPointSignedMoment second‖ +
            ‖centrallySymmetricFourPoint (fourPointOddPart first).1 (fourPointOddPart first).2 -
              centrallySymmetricFourPoint (fourPointOddPart second).1 (fourPointOddPart second).2‖ *
                ‖fourPointSignedMoment second‖ ^ 2) / 16 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointOddInternalError_uniform_annular_relative_bound lowerPositive ordered upperSmall
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient scale first second scaleNonzero secondPositive secondLower secondUpper firstNoncollision small
  have secondNoncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (fourPointOddPart second).1 (fourPointOddPart second).2) := by
    rw [secondPositive]
    exact normalized_central_noncollision (lowerPositive.trans_le secondLower) (secondUpper.trans_lt upperSmall)
  have actual := estimate 1 (fourPointOddPart first).1 (fourPointOddPart first).2
    (fourPointOddPart second).2 (fourPointSignedMoment first / 4) (fourPointSignedMoment second / 4)
    secondLower secondUpper firstNoncollision (by
      simp only [norm_div, Complex.norm_ofNat, ← add_div]
      simpa only [secondPositive] using small)
  rw [← secondPositive, ← fourPointOddInternalError_balanced, ← fourPointOddInternalError_balanced] at actual
  have centerDifference : fourPointSignedMoment first / 4 - fourPointSignedMoment second / 4 =
      (fourPointSignedMoment first - fourPointSignedMoment second) / 4 := by ring
  rw [centerDifference] at actual
  simp only [norm_div, Complex.norm_ofNat, abs_one, mul_one] at actual
  rw [fourPointOddInternalError_dilation coefficient scaleNonzero first firstNoncollision,
    fourPointOddInternalError_dilation coefficient scaleNonzero second secondNoncollision, ← smul_sub,
    norm_smul, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_star]
  exact (mul_le_mul_of_nonneg_left actual (by positivity : 0 ≤ |coefficient| / ‖scale‖)).trans_eq (by ring)

end EulerNonuniqueness.Section6
