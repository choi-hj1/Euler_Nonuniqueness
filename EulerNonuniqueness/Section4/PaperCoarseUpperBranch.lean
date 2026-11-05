import EulerNonuniqueness.Section6.PaperShapeBranch

noncomputable section

namespace EulerNonuniqueness.Paper

theorem paper_shape_ratio_im_pos_of_small {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count)
    (small : |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4) :
    0 < (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index).im := by
  let ratio := negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index
  have angularIdentity : angularShape motion time index = unstableShape motion time index - stableShape motion time index := by
    dsimp only [unstableShape, stableShape]
    ring
  have angularBound : |angularShape motion time index| ≤ 1 / 4 := by
    rw [angularIdentity]
    exact (abs_sub _ _).trans small
  have sqrtPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have sqrtSmall : Real.sqrt 2 < 2 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have rawLower := (le_div_iff₀ sqrtPositive).mp (abs_le.mp angularBound).1
  have rawUpper := (div_le_iff₀ sqrtPositive).mp (abs_le.mp angularBound).2
  change -(1 / 4 : ℝ) * Real.sqrt 2 ≤ 2 * Complex.arg ratio - Real.pi at rawLower
  change 2 * Complex.arg ratio - Real.pi ≤ (1 / 4 : ℝ) * Real.sqrt 2 at rawUpper
  have argPositive : 0 < Complex.arg ratio := by linarith only [rawLower, sqrtSmall, Real.pi_gt_three]
  have argSmall : Complex.arg ratio < Real.pi := by linarith only [rawUpper, sqrtSmall, Real.pi_gt_three]
  have nonzero : ratio ≠ 0 := by
    intro zero
    rw [zero, Complex.arg_zero] at argPositive
    exact lt_irrefl 0 argPositive
  rw [← Complex.norm_mul_sin_arg ratio]
  exact mul_pos (norm_pos_iff.mpr nonzero) (Real.sin_pos_of_pos_of_lt_pi argPositive argSmall)

end EulerNonuniqueness.Paper
