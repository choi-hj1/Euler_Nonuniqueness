import EulerNonuniqueness.Section4.RegularizedShapeCoordinates
import EulerNonuniqueness.Section6.ReferenceChartImaginaryGap

noncomputable section

namespace EulerNonuniqueness.Paper

theorem regularizedShapeCoordinates_square_left {denominatorFloor : ℝ} {positive negative : ℂ}
    (denominatorLower : denominatorFloor ≤ ‖positive‖ ^ 2)
    (small : |(regularizedShapeCoordinates denominatorFloor (1 / 16) positive negative).1| +
      |(regularizedShapeCoordinates denominatorFloor (1 / 16) positive negative).2| ≤ 1 / 4) :
    (((negative / positive) ^ 2) : ℂ).re < 0 := by
  let coordinates := regularizedShapeCoordinates denominatorFloor (1 / 16) positive negative
  let quotient := negative / positive
  let clamped := upperHalfPlaneClamp (1 / 16) quotient
  have rootSquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have rootNonnegative := Real.sqrt_nonneg (2 : ℝ)
  have rootPositive := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have rootUpper : Real.sqrt 2 ≤ (35 / 24 : ℝ) := by nlinarith
  have rhombusLower : (1 / 12 : ℝ) ≤ rhombusRatio := by unfold rhombusRatio; linarith
  have rhombusPositive : 0 < rhombusRatio := Section2.rhombusRatio_pos
  have radialIdentity : rhombusRatio * (1 + coordinates.1 + coordinates.2) = ‖quotient‖ ^ 2 := by
    dsimp only [coordinates, regularizedShapeCoordinates, quotient]
    rw [max_eq_right denominatorLower, norm_div, div_pow]
    field_simp [rhombusPositive.ne']
    <;> ring
  have sumLower : (3 / 4 : ℝ) ≤ 1 + coordinates.1 + coordinates.2 := by
    linarith [neg_abs_le coordinates.1, neg_abs_le coordinates.2]
  have ratioLower : (1 / 16 : ℝ) ≤ ‖quotient‖ ^ 2 := by
    have multiplied := mul_le_mul_of_nonneg_left sumLower rhombusPositive.le
    rw [radialIdentity] at multiplied
    nlinarith
  have angularIdentity : Real.sqrt 2 * (coordinates.1 - coordinates.2) = 2 * clamped.arg - Real.pi := by
    dsimp only [coordinates, regularizedShapeCoordinates, clamped, quotient]
    rw [regularizedDiagonalRatio_eq_of_lower_bound denominatorLower]
    field_simp [rootPositive.ne']
    <;> ring
  have differenceBound : |coordinates.1 - coordinates.2| ≤ 1 / 4 := (abs_sub _ _).trans small
  have displacement : |2 * clamped.arg - Real.pi| ≤ 1 / 2 := by
    rw [← angularIdentity, abs_mul, abs_of_nonneg rootNonnegative]
    have multiplied := mul_le_mul rootUpper differenceBound (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 35 / 24)
    nlinarith
  have lower : Real.pi / 2 < 2 * clamped.arg := by linarith [(abs_le.mp displacement).1, Real.pi_gt_three]
  have upper : 2 * clamped.arg < Real.pi + Real.pi / 2 := by linarith [(abs_le.mp displacement).2, Real.pi_gt_three]
  have cosineNegative := Real.cos_neg_of_pi_div_two_lt_of_lt lower upper
  rw [Real.cos_two_mul] at cosineNegative
  have clampedImaginary : (1 / 16 : ℝ) ≤ clamped.im := le_max_left _ _
  have clampedNonzero : clamped ≠ 0 := by intro zero; simp only [zero, Complex.zero_im] at clampedImaginary; norm_num at clampedImaginary
  have normPositive := sq_pos_of_pos (norm_pos_iff.mpr clampedNonzero)
  have multiplied := mul_neg_of_pos_of_neg normPositive cosineNegative
  have realSquare : clamped.re ^ 2 = ‖clamped‖ ^ 2 * Real.cos clamped.arg ^ 2 := by
    rw [← Complex.norm_mul_cos_arg clamped]
    ring
  have normIdentity : ‖clamped‖ ^ 2 = clamped.re ^ 2 + clamped.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have clampedLeft : clamped.re ^ 2 < clamped.im ^ 2 := by nlinarith only [multiplied, realSquare, normIdentity]
  have quotientNorm : ‖quotient‖ ^ 2 = quotient.re ^ 2 + quotient.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have actualLeft : quotient.re ^ 2 < quotient.im ^ 2 := by
    by_cases imaginaryLower : (1 / 16 : ℝ) ≤ quotient.im
    · simpa only [clamped, upperHalfPlaneClamp_eq_of_lower_bound imaginaryLower] using clampedLeft
    · have imaginaryUpper : quotient.im ≤ 1 / 16 := (lt_of_not_ge imaginaryLower).le
      have clampedReal : clamped.re = quotient.re := rfl
      have clampedImaginaryValue : clamped.im = 1 / 16 := max_eq_left imaginaryUpper
      rw [clampedReal, clampedImaginaryValue] at clampedLeft
      nlinarith only [ratioLower, quotientNorm, clampedLeft]
  simpa only [pow_two, Complex.mul_re] using sub_neg.mpr actualLeft

theorem regularizedShapeCoordinates_ratio_normSq_lower {denominatorFloor : ℝ} {positive negative : ℂ}
    (denominatorLower : denominatorFloor ≤ ‖positive‖ ^ 2)
    (small : |(regularizedShapeCoordinates denominatorFloor (1 / 16) positive negative).1| +
      |(regularizedShapeCoordinates denominatorFloor (1 / 16) positive negative).2| ≤ 1 / 4) :
    (1 / 16 : ℝ) ≤ ‖negative / positive‖ ^ 2 := by
  let coordinates := regularizedShapeCoordinates denominatorFloor (1 / 16) positive negative
  have rhombusPositive : 0 < rhombusRatio := Section2.rhombusRatio_pos
  have rhombusLower : (1 / 12 : ℝ) ≤ rhombusRatio := by
    unfold rhombusRatio
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have radialIdentity : rhombusRatio * (1 + coordinates.1 + coordinates.2) = ‖negative / positive‖ ^ 2 := by
    dsimp only [coordinates, regularizedShapeCoordinates]
    rw [max_eq_right denominatorLower, norm_div, div_pow]
    field_simp [rhombusPositive.ne'] <;> ring
  have sumLower : (3 / 4 : ℝ) ≤ 1 + coordinates.1 + coordinates.2 := by
    linarith [neg_abs_le coordinates.1, neg_abs_le coordinates.2]
  have multiplied := mul_le_mul_of_nonneg_left sumLower rhombusPositive.le
  rw [radialIdentity] at multiplied
  nlinarith

theorem regularizedShapeCoordinates_eq_paper_of_small_upper {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) {denominatorFloor : ℝ}
    (denominatorLower : denominatorFloor ≤ ‖positiveHalfDiagonal motion time index‖ ^ 2)
    (small : |(regularizedShapeCoordinates denominatorFloor (1 / 16)
      (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).1| +
      |(regularizedShapeCoordinates denominatorFloor (1 / 16)
      (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).2| ≤ 1 / 4)
    (upper : 0 < (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index).im) :
    regularizedShapeCoordinates denominatorFloor (1 / 16)
      (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) =
        (unstableShape motion time index, stableShape motion time index) := by
  let quotient := negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index
  have ratioLower := regularizedShapeCoordinates_ratio_normSq_lower denominatorLower small
  have left := regularizedShapeCoordinates_square_left denominatorLower small
  change (quotient ^ 2).re < 0 at left
  simp only [pow_two, Complex.mul_re] at left
  have normIdentity : ‖quotient‖ ^ 2 = quotient.re ^ 2 + quotient.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have imaginaryLower : (1 / 16 : ℝ) ≤ quotient.im := by
    change (1 / 16 : ℝ) ≤ ‖quotient‖ ^ 2 at ratioLower
    change 0 < quotient.im at upper
    nlinarith
  exact regularizedShapeCoordinates_eq_paper motion time index denominatorLower imaginaryLower

end EulerNonuniqueness.Paper
