import Mathlib

namespace EulerNonuniqueness.General

noncomputable section

open Set Metric
open scoped NNReal

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem norm_quadratic_remainder_of_lipschitz_derivative
    (function : Space → Target) (derivative : Space → Space →L[ℝ] Target)
    {radius : ℝ} (constant : ℝ≥0)
    (actual : ∀ value ∈ closedBall (0 : Space) radius, HasFDerivAt function (derivative value) value)
    (lipschitz : LipschitzOnWith constant derivative (closedBall (0 : Space) radius))
    (base increment : Space) (inside : ‖base‖ + ‖increment‖ ≤ radius) :
    ‖function (base + increment) - function base - derivative base increment‖ ≤
      (constant : ℝ) * ‖increment‖ ^ 2 := by
  have contained : closedBall base ‖increment‖ ⊆ closedBall (0 : Space) radius := by
    intro point member
    apply mem_closedBall_zero_iff.mpr
    have distance := mem_closedBall.mp member
    rw [dist_eq_norm point base] at distance
    have triangle := norm_add_le (point - base) base
    rw [sub_add_cancel] at triangle
    linarith
  have baseInside : base ∈ closedBall (0 : Space) radius :=
    contained (mem_closedBall_self (norm_nonneg increment))
  let remainder := fun point => function point - derivative base point
  have derivativeActual (point : Space) (member : point ∈ closedBall base ‖increment‖) :
      HasFDerivAt remainder (derivative point - derivative base) point :=
    (actual point (contained member)).sub ((derivative base).hasFDerivAt (x := point))
  have derivativeBound (point : Space) (member : point ∈ closedBall base ‖increment‖) :
      ‖derivative point - derivative base‖ ≤ (constant : ℝ) * ‖increment‖ := by
    have bound := LipschitzOnWith.norm_sub_le (f := derivative) lipschitz (contained member) baseInside
    have distance := mem_closedBall.mp member
    rw [dist_eq_norm point base] at distance
    exact bound.trans (mul_le_mul_of_nonneg_left distance constant.coe_nonneg)
  have endpoint : base + increment ∈ closedBall base ‖increment‖ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have estimate := (convex_closedBall base ‖increment‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun point member => (derivativeActual point member).hasFDerivWithinAt) derivativeBound
    (mem_closedBall_self (norm_nonneg increment)) endpoint
  have identity : remainder (base + increment) - remainder base =
      function (base + increment) - function base - derivative base increment := by
    dsimp [remainder]
    rw [map_add]
    abel
  rw [identity, add_sub_cancel_left] at estimate
  simpa only [pow_two, mul_assoc] using estimate

end

end EulerNonuniqueness.General
