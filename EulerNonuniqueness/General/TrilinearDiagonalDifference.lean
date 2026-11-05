import EulerNonuniqueness.General.CubicFiberCoefficient

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace
  cubicCoefficientThirdGroup cubicCoefficientThirdSpace

theorem norm_trilinear_diagonal_difference_le
    (initial final : Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Space)
    (first second : Space) :
    ‖initial first first first - final second second second‖ ≤
      ‖initial‖ * (‖first‖ + ‖second‖) ^ 2 * ‖first - second‖ +
        ‖initial - final‖ * ‖second‖ ^ 3 := by
  have telescope : initial first first first - final second second second =
      initial (first - second) first first + initial second (first - second) first +
        initial second second (first - second) + (initial - final) second second second := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  have bound (linear : Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Space)
      (left middle right : Space) :
      ‖linear left middle right‖ ≤ ‖linear‖ * ‖left‖ * ‖middle‖ * ‖right‖ := by
    exact (linear left middle).le_opNorm right |>.trans
      (mul_le_mul_of_nonneg_right ((linear left).le_opNorm middle |>.trans
        (mul_le_mul_of_nonneg_right (linear.le_opNorm left) (norm_nonneg middle)))
        (norm_nonneg right))
  rw [telescope]
  calc
    _ ≤ ‖initial (first - second) first first‖ + ‖initial second (first - second) first‖ +
        ‖initial second second (first - second)‖ + ‖(initial - final) second second second‖ :=
      (norm_add_le _ _).trans (add_le_add_right ((norm_add_le _ _).trans
        (add_le_add_right (norm_add_le _ _) _)) _)
    _ ≤ ‖initial‖ * ‖first - second‖ * ‖first‖ * ‖first‖ +
        ‖initial‖ * ‖second‖ * ‖first - second‖ * ‖first‖ +
        ‖initial‖ * ‖second‖ * ‖second‖ * ‖first - second‖ +
        ‖initial - final‖ * ‖second‖ * ‖second‖ * ‖second‖ :=
      add_le_add (add_le_add (add_le_add (bound _ _ _ _) (bound _ _ _ _)) (bound _ _ _ _))
        (bound _ _ _ _)
    _ ≤ _ := by
      have nonnegative : 0 ≤ ‖initial‖ * ‖first‖ * ‖second‖ * ‖first - second‖ := by positivity
      nlinarith

end

end EulerNonuniqueness.General
