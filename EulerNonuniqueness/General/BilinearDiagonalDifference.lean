import EulerNonuniqueness.General.CubicFiberCoefficient

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace

theorem norm_bilinear_diagonal_difference_le (first second : BilinearEnd Space) (initial final : Space) :
    ‖first initial initial - second final final‖ ≤
      ‖first‖ * (‖initial‖ + ‖final‖) * ‖initial - final‖ +
        ‖first - second‖ * ‖final‖ ^ 2 := by
  have estimate (operator : BilinearEnd Space) (left right : Space) :
      ‖operator left right‖ ≤ ‖operator‖ * ‖left‖ * ‖right‖ :=
    (operator left).le_opNorm right |>.trans
      (mul_le_mul_of_nonneg_right (operator.le_opNorm left) (norm_nonneg right))
  have identity : first initial initial - second final final =
      first (initial - final) initial + first final (initial - final) + (first - second) final final := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [identity]
  calc
    _ ≤ (‖first (initial - final) initial‖ + ‖first final (initial - final)‖) +
        ‖(first - second) final final‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ (‖first‖ * ‖initial - final‖ * ‖initial‖ + ‖first‖ * ‖final‖ * ‖initial - final‖) +
        ‖first - second‖ * ‖final‖ * ‖final‖ :=
      add_le_add (add_le_add (estimate _ _ _) (estimate _ _ _)) (estimate _ _ _)
    _ = _ := by ring

end

end EulerNonuniqueness.General
