import Mathlib.Analysis.Calculus.MeanValue

namespace EulerNonuniqueness.General

noncomputable section

open Set Metric

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem stationary_remainder_transverse_factor
    (remainder : Domain → Range) (derivative : Domain → Domain →L[ℝ] Range)
    {constant radius : ℝ} (constantNonnegative : 0 ≤ constant)
    (actualDerivative : ∀ value ∈ closedBall (0 : Domain) radius,
      HasFDerivAt remainder (derivative value) value)
    (derivativeBound : ∀ value ∈ closedBall (0 : Domain) radius,
      ‖derivative value‖ ≤ constant * ‖value‖ ^ 2)
    (neutral transverse : Domain) (inside : ‖neutral‖ + ‖transverse‖ ≤ radius)
    (stationary : remainder neutral = 0) :
    ‖remainder (neutral + transverse)‖ ≤
      constant * (‖neutral‖ + ‖transverse‖) ^ 2 * ‖transverse‖ := by
  let size := ‖neutral‖ + ‖transverse‖
  have subset : closedBall (0 : Domain) size ⊆ closedBall (0 : Domain) radius := by
    intro value member
    rw [mem_closedBall_zero_iff] at member ⊢
    exact member.trans inside
  have bounded (value : Domain) (member : value ∈ closedBall (0 : Domain) size) :
      ‖derivative value‖ ≤ constant * size ^ 2 := by
    apply (derivativeBound value (subset member)).trans
    apply mul_le_mul_of_nonneg_left _ constantNonnegative
    apply pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp member)
  have neutralInside : neutral ∈ closedBall (0 : Domain) size := by
    rw [mem_closedBall_zero_iff]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have totalInside : neutral + transverse ∈ closedBall (0 : Domain) size := by
    rw [mem_closedBall_zero_iff]
    exact norm_add_le _ _
  have actual := (convex_closedBall (0 : Domain) size).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun value member => (actualDerivative value (subset member)).hasFDerivWithinAt) bounded neutralInside totalInside
  simpa only [stationary, sub_zero, add_sub_cancel_left] using actual

end

end EulerNonuniqueness.General
