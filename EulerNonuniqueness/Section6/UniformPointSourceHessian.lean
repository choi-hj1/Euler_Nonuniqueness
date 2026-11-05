import EulerNonuniqueness.Section6.PhysicalPointHessian

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem twoDipole_receiver_ball_separation
    {firstCenter secondCenter firstSeparation secondSeparation receiverCenter : ℂ}
    {length receiverRadius : ℝ} (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (separated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (far : 4 * ‖firstCenter - secondCenter‖ ≤ ‖receiverCenter - (firstCenter + secondCenter) / 2‖)
    (receiverSmall : receiverRadius ≤ ‖receiverCenter - (firstCenter + secondCenter) / 2‖ / 2) :
    ∀ location ∈ Metric.closedBall receiverCenter receiverRadius,
      ‖receiverCenter - (firstCenter + secondCenter) / 2‖ / 2 ≤ ‖location - (firstCenter + secondCenter) / 2‖ ∧
      ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2 ∧
      ∀ target, location - twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target ≠ 0 := by
  intro location member
  have localRadius : ‖location - receiverCenter‖ ≤ receiverRadius := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using member
  have triangle := norm_add_le (receiverCenter - location) (location - (firstCenter + secondCenter) / 2)
  rw [sub_add_sub_cancel, norm_sub_rev receiverCenter location] at triangle
  have lower : ‖receiverCenter - (firstCenter + secondCenter) / 2‖ / 2 ≤
      ‖location - (firstCenter + secondCenter) / 2‖ := by linarith
  have localFar : ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2 := by linarith
  refine ⟨lower, localFar, ?_⟩
  intro target zero
  have equality := sub_eq_zero.mp zero
  have sourceInside := twoDipole_mem_center_ball
    (firstCenter := firstCenter) (secondCenter := secondCenter)
    (firstSeparation := firstSeparation) (secondSeparation := secondSeparation)
    (firstBound.trans (by linarith)) (secondBound.trans (by linarith)) target
  have sourceRadius : ‖twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target -
      (firstCenter + secondCenter) / 2‖ ≤ ‖firstCenter - secondCenter‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using sourceInside
  rw [← equality] at sourceRadius
  linarith

theorem twoDipole_source_fderiv_lipschitz_on_ball (coefficient : ℝ)
    {firstCenter secondCenter firstSeparation secondSeparation receiverCenter : ℂ}
    {length receiverRadius : ℝ} {bound : ℝ≥0}
    (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (separated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (far : 4 * ‖firstCenter - secondCenter‖ ≤ ‖receiverCenter - (firstCenter + secondCenter) / 2‖)
    (receiverSmall : receiverRadius ≤ ‖receiverCenter - (firstCenter + secondCenter) / 2‖ / 2)
    (boundLarge : |coefficient| * (96 * ‖firstSeparation + secondSeparation‖ /
        ‖receiverCenter - (firstCenter + secondCenter) / 2‖ ^ 4 +
      151040 * ‖firstCenter - secondCenter‖ * length /
        ‖receiverCenter - (firstCenter + secondCenter) / 2‖ ^ 5) ≤ bound) :
    LipschitzOnWith bound
      (fderiv ℝ (fourPointExternalPointVelocity coefficient
        (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation)))
      (Metric.closedBall receiverCenter receiverRadius) := by
  have geometry := twoDipole_receiver_ball_separation lengthPositive firstBound secondBound separated far receiverSmall
  apply fourPointExternalPointVelocity_fderiv_lipschitz coefficient _ (convex_closedBall _ _)
    (fun location member => (geometry location member).2.2)
  intro location member
  have localGeometry := geometry location member
  have estimate := twoDipole_physical_hessian_moment_bound coefficient lengthPositive firstBound secondBound separated localGeometry.2.1
  apply estimate.trans
  apply le_trans _ boundLarge
  let distance := ‖receiverCenter - (firstCenter + secondCenter) / 2‖
  have distancePositive : 0 < distance := by dsimp [distance]; nlinarith
  have halfPositive : 0 < distance / 2 := by positivity
  have lower := localGeometry.1
  have firstControl : 6 * ‖firstSeparation + secondSeparation‖ /
      ‖location - (firstCenter + secondCenter) / 2‖ ^ 4 ≤
      96 * ‖firstSeparation + secondSeparation‖ / distance ^ 4 := by
    calc
      _ ≤ 6 * ‖firstSeparation + secondSeparation‖ / (distance / 2) ^ 4 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos halfPositive 4) (pow_le_pow_left₀ halfPositive.le lower 4)
      _ = _ := by field_simp [distancePositive.ne']; ring
  have secondControl : 4720 * ‖firstCenter - secondCenter‖ * length /
      ‖location - (firstCenter + secondCenter) / 2‖ ^ 5 ≤
      151040 * ‖firstCenter - secondCenter‖ * length / distance ^ 5 := by
    calc
      _ ≤ 4720 * ‖firstCenter - secondCenter‖ * length / (distance / 2) ^ 5 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos halfPositive 5) (pow_le_pow_left₀ halfPositive.le lower 5)
      _ = _ := by field_simp [distancePositive.ne']; ring
  exact mul_le_mul_of_nonneg_left (add_le_add firstControl secondControl) (abs_nonneg coefficient)

end EulerNonuniqueness.Section6
