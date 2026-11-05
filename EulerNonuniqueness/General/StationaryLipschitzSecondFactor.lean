import EulerNonuniqueness.General.StationaryPowerFactor

namespace EulerNonuniqueness.General

noncomputable section

open Set Metric
open scoped NNReal

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem derivative_quadratic_bound_of_lipschitz_second
    (derivative : Domain → Domain →L[ℝ] Range)
    (second : Domain → Domain →L[ℝ] Domain →L[ℝ] Range)
    {radius : ℝ} (radiusNonnegative : 0 ≤ radius) (constant : ℝ≥0)
    (actual : ∀ value ∈ closedBall (0 : Domain) radius,
      HasFDerivAt derivative (second value) value)
    (lipschitz : LipschitzOnWith constant second (closedBall (0 : Domain) radius))
    (flat : derivative (0 : Domain) = 0) (secondFlat : second (0 : Domain) = 0)
    (value : Domain) (inside : value ∈ closedBall (0 : Domain) radius) :
    ‖derivative value‖ ≤ (constant : ℝ) * ‖value‖ ^ 2 := by
  have zeroInside : (0 : Domain) ∈ closedBall (0 : Domain) radius := mem_closedBall_self radiusNonnegative
  have estimate (point : Domain) (member : point ∈ closedBall (0 : Domain) radius) :
      ‖second point‖ ≤ (constant : ℝ) * ‖point‖ := by
    have normBound : ‖second point - second (0 : Domain)‖ ≤ (constant : ℝ) * ‖point - (0 : Domain)‖ :=
      LipschitzOnWith.norm_sub_le (f := second) lipschitz member zeroInside
    simpa only [secondFlat, sub_zero] using normBound
  have contained : closedBall (0 : Domain) ‖value‖ ⊆ closedBall (0 : Domain) radius := by
    intro point member
    exact mem_closedBall_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp member).trans (mem_closedBall_zero_iff.mp inside))
  have bound := (convex_closedBall (0 : Domain) ‖value‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun point member => (actual point (contained member)).hasFDerivWithinAt)
    (fun point member => (estimate point (contained member)).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp member) constant.coe_nonneg))
    (mem_closedBall_self (norm_nonneg value))
    (mem_closedBall_zero_iff.mpr (le_refl ‖value‖))
  simpa only [flat, sub_zero, ← pow_two, mul_assoc] using bound

theorem stationary_transverse_cubic_factor_of_lipschitz_second
    (remainder : Domain → Range) (derivative : Domain → Domain →L[ℝ] Range)
    (second : Domain → Domain →L[ℝ] Domain →L[ℝ] Range)
    {radius : ℝ} (radiusNonnegative : 0 ≤ radius) (constant : ℝ≥0)
    (actualFirst : ∀ value ∈ closedBall (0 : Domain) radius,
      HasFDerivAt remainder (derivative value) value)
    (actualSecond : ∀ value ∈ closedBall (0 : Domain) radius,
      HasFDerivAt derivative (second value) value)
    (lipschitz : LipschitzOnWith constant second (closedBall (0 : Domain) radius))
    (flat : derivative (0 : Domain) = 0) (secondFlat : second (0 : Domain) = 0)
    (neutral transverse : Domain) (inside : ‖neutral‖ + ‖transverse‖ ≤ radius)
    (stationary : remainder neutral = 0) :
    ‖remainder (neutral + transverse)‖ ≤
      (constant : ℝ) * (‖neutral‖ + ‖transverse‖) ^ 2 * ‖transverse‖ := by
  exact stationary_remainder_transverse_power_factor remainder derivative 2 constant.coe_nonneg
    actualFirst (derivative_quadratic_bound_of_lipschitz_second derivative second radiusNonnegative
      constant actualSecond lipschitz flat secondFlat) neutral transverse inside stationary

end

end EulerNonuniqueness.General
