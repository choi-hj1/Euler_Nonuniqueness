import EulerNonuniqueness.Section6.RelativePointShapeChart

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem pointShapeChart_reference_annulus (positive negative : ℂ)
    (small : |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| ≤ 1 / 4) :
    positive ≠ 0 ∧ negative ≠ 0 ∧
      (1 / 4 : ℝ) ≤ ‖negative‖ / ‖positive‖ ∧ ‖negative‖ / ‖positive‖ ≤ 1 / 2 := by
  have rootSquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have rootNonnegative := Real.sqrt_nonneg (2 : ℝ)
  have rootLower : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have rootUpper : Real.sqrt 2 ≤ (35 / 24 : ℝ) := by nlinarith
  have rhombusLower : (1 / 12 : ℝ) ≤ rhombusRatio := by unfold rhombusRatio; linarith
  have rhombusUpper : rhombusRatio ≤ (1 / 5 : ℝ) := by unfold rhombusRatio; linarith
  have reconstruction := (shapeChart_reconstruction (pointShapeRatio positive negative)
    (pointShapeAngle positive negative)).1
  change rhombusRatio * (1 + (pointShapeChart positive negative).1 +
    (pointShapeChart positive negative).2) = pointShapeRatio positive negative at reconstruction
  have sumLower : (3 / 4 : ℝ) ≤ 1 + (pointShapeChart positive negative).1 +
      (pointShapeChart positive negative).2 := by
    linarith [neg_abs_le (pointShapeChart positive negative).1, neg_abs_le (pointShapeChart positive negative).2]
  have sumUpper : 1 + (pointShapeChart positive negative).1 +
      (pointShapeChart positive negative).2 ≤ (5 / 4 : ℝ) := by
    linarith [le_abs_self (pointShapeChart positive negative).1, le_abs_self (pointShapeChart positive negative).2]
  have ratioLower : (1 / 16 : ℝ) ≤ pointShapeRatio positive negative := by
    have multiplied := mul_le_mul_of_nonneg_left sumLower rhombusRatio_pos.le
    rw [reconstruction] at multiplied
    nlinarith
  have ratioUpper : pointShapeRatio positive negative ≤ (1 / 4 : ℝ) := by
    have multiplied := mul_le_mul_of_nonneg_left sumUpper rhombusRatio_pos.le
    rw [reconstruction] at multiplied
    nlinarith
  have squareIdentity : (‖negative‖ / ‖positive‖) ^ 2 = pointShapeRatio positive negative := by
    rw [div_pow]
    rfl
  have ratioNonnegative : 0 ≤ ‖negative‖ / ‖positive‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have normLower : (1 / 4 : ℝ) ≤ ‖negative‖ / ‖positive‖ := by nlinarith
  have normUpper : ‖negative‖ / ‖positive‖ ≤ (1 / 2 : ℝ) := by nlinarith
  refine ⟨?_, ?_, normLower, normUpper⟩
  · intro zero
    simp only [zero, norm_zero, div_zero] at normLower
    norm_num at normLower
  · intro zero
    simp only [zero, norm_zero, zero_div] at normLower
    norm_num at normLower

end EulerNonuniqueness.Section6
