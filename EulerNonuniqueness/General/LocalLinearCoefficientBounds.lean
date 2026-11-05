import EulerNonuniqueness.General.LocalLipschitzCenteredBounds
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic

noncomputable section

namespace EulerNonuniqueness.General

variable {Domain Coefficient Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Coefficient] [NormedSpace ℝ Coefficient]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem LipschitzNear.exists_uniform_linear_coefficient_ball
    {function : Domain → Coefficient →L[ℝ] Target} {center : Domain}
    (regular : LipschitzNear function center) :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ point, ‖point - center‖ ≤ radius → ∀ coefficient,
        ‖function point coefficient‖ ≤ constant * ‖coefficient‖) ∧
      ∀ first second, ‖first - center‖ ≤ radius → ‖second - center‖ ≤ radius → ∀ coefficient,
        ‖function first coefficient - function second coefficient‖ ≤
          constant * ‖coefficient‖ * ‖first - second‖ := by
  obtain ⟨outer, positive, lipschitzConstant, constantOne, difference⟩ :=
    regular.exists_centered_closedBall_difference_bound
  let constant := lipschitzConstant + ‖function center‖ + 1
  have constantLarge : lipschitzConstant ≤ constant := by
    dsimp [constant]
    linarith [norm_nonneg (function center)]
  refine ⟨min outer 1, lt_min positive zero_lt_one, constant, by dsimp [constant]; linarith [norm_nonneg (function center)], ?_, ?_⟩
  · intro point inside coefficient
    have deviation := difference point center (inside.trans (min_le_left _ _))
      (by simpa only [sub_self, norm_zero] using positive.le)
    have bound : ‖function point‖ ≤ constant := by
      have triangle : ‖function point‖ ≤ ‖function point - function center‖ + ‖function center‖ := by
        simpa only [sub_add_cancel] using norm_add_le (function point - function center) (function center)
      have distanceOne := inside.trans (min_le_right outer 1)
      have enlarged := deviation.trans (mul_le_mul_of_nonneg_left distanceOne (by linarith))
      dsimp [constant]
      linarith
    exact (function point).le_opNorm coefficient |>.trans
      (mul_le_mul_of_nonneg_right bound (norm_nonneg coefficient))
  · intro first second firstInside secondInside coefficient
    have deviation := difference first second (firstInside.trans (min_le_left _ _))
      (secondInside.trans (min_le_left _ _))
    have applied : ‖function first coefficient - function second coefficient‖ ≤
        ‖function first - function second‖ * ‖coefficient‖ := by
      exact (function first - function second).le_opNorm coefficient
    exact applied.trans ((mul_le_mul_of_nonneg_right
      (deviation.trans (mul_le_mul_of_nonneg_right constantLarge (norm_nonneg _)))
      (norm_nonneg coefficient)).trans_eq (by ring))

end EulerNonuniqueness.General
