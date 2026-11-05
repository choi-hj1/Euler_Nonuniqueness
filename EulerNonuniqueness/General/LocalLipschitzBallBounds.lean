import EulerNonuniqueness.Section3.LocalLipschitzCalculus

noncomputable section

open Set Metric
open scoped Topology

namespace EulerNonuniqueness.General

variable {Domain Target : Type*} [NormedAddCommGroup Domain] [NormedAddCommGroup Target]

theorem LipschitzNear.exists_closedBall_bounds {function : Domain → Target}
    (regular : LipschitzNear function (0 : Domain)) :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ point : Domain, ‖point‖ ≤ radius → ‖function point‖ ≤ constant) ∧
      ∀ first second : Domain, ‖first‖ ≤ radius → ‖second‖ ≤ radius →
        ‖function first - function second‖ ≤ constant * ‖first - second‖ := by
  obtain ⟨lipschitzConstant, neighborhood, nearby, lipschitz⟩ := regular
  obtain ⟨outerRadius, positive, contained⟩ := Metric.mem_nhds_iff.mp nearby
  let radius := outerRadius / 2
  let constant : ℝ := 1 + lipschitzConstant + ‖function 0‖ + lipschitzConstant * radius
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have constantOne : 1 ≤ constant := by
    have productNonnegative : 0 ≤ (lipschitzConstant : ℝ) * radius := by positivity
    dsimp [constant]
    linarith [lipschitzConstant.coe_nonneg, norm_nonneg (function 0)]
  have constantLip : (lipschitzConstant : ℝ) ≤ constant := by
    dsimp [constant]
    have productNonnegative : 0 ≤ (lipschitzConstant : ℝ) * radius := by positivity
    linarith [norm_nonneg (function 0)]
  have inside (point : Domain) (bound : ‖point‖ ≤ radius) : point ∈ neighborhood := by
    apply contained
    rw [Metric.mem_ball, dist_zero_right]
    exact bound.trans_lt (by dsimp [radius]; linarith)
  have zeroInside := inside 0 (by simpa using radiusPositive.le)
  refine ⟨radius, radiusPositive, constant, constantOne, ?_, ?_⟩
  · intro point bound
    have difference := lipschitz.norm_sub_le (inside point bound) zeroInside
    rw [sub_zero] at difference
    calc
      ‖function point‖ ≤ ‖function point - function 0‖ + ‖function 0‖ := by
        calc
          _ = ‖(function point - function 0) + function 0‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      _ ≤ (lipschitzConstant : ℝ) * radius + ‖function 0‖ :=
        add_le_add_right (difference.trans
          (mul_le_mul_of_nonneg_left bound lipschitzConstant.coe_nonneg)) _
      _ ≤ constant := by dsimp [constant]; linarith [lipschitzConstant.coe_nonneg]
  · intro first second firstBound secondBound
    exact (lipschitz.norm_sub_le (inside first firstBound) (inside second secondBound)).trans
      (mul_le_mul_of_nonneg_right constantLip (norm_nonneg _))

end EulerNonuniqueness.General
