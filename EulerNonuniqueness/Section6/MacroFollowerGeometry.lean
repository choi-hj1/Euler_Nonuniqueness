import EulerNonuniqueness.Section6.MovingQuadrupoleMacroCoefficientBound

noncomputable section

namespace EulerNonuniqueness.Paper

theorem macro_follower_centroid_clearance {receiverCenter sourceCenter receiverPoint sourcePoint frozen : ℂ}
    {receiverScale sourceScale gap : ℝ} (gapNonnegative : 0 ≤ gap)
    (frozenNorm : ‖frozen‖ = gap) (scalesBound : receiverScale + sourceScale ≤ 3 * gap)
    (aligned : ‖(receiverPoint - sourceCenter) - frozen‖ ≤ 3 * gap / 16)
    (receiverExtent : ‖receiverPoint - receiverCenter‖ ≤ receiverScale / 100)
    (sourceExtent : ‖sourcePoint - sourceCenter‖ ≤ sourceScale / 100) :
    gap / 8 ≤ ‖receiverCenter - sourcePoint‖ := by
  have first := norm_sub_le_norm_sub_add_norm_sub frozen (receiverPoint - sourceCenter) 0
  rw [sub_zero, sub_zero, norm_sub_rev frozen (receiverPoint - sourceCenter), frozenNorm] at first
  have second := norm_sub_le_norm_sub_add_norm_sub receiverPoint receiverCenter sourceCenter
  have third := norm_sub_le_norm_sub_add_norm_sub receiverCenter sourcePoint sourceCenter
  linarith

theorem signed_circle_mass_budget {density radius circulation sign : ℝ}
    (circulationNonnegative : 0 ≤ circulation) (signAbs : |sign| = 1)
    (mass : density * (Real.pi * radius ^ 2) = circulation * sign) :
    |density| * radius ^ 2 ≤ circulation := by
  have actual := congrArg abs mass
  simp only [abs_mul, abs_of_nonneg circulationNonnegative, signAbs, mul_one,
    abs_of_pos Real.pi_pos, abs_sq] at actual
  have enlarged := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_three])
    (mul_nonneg (abs_nonneg density) (sq_nonneg radius))
  nlinarith

end EulerNonuniqueness.Paper
