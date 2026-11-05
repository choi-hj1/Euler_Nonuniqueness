import EulerNonuniqueness.Section6.SignedExteriorMomentSeries
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem complex_power_difference_bound (first second : ℂ) (power : ℕ) {radius : ℝ}
    (nonnegative : 0 ≤ radius) (firstBound : ‖first‖ ≤ radius) (secondBound : ‖second‖ ≤ radius) :
    ‖first ^ (power + 1) - second ^ (power + 1)‖ ≤
      (power + 1 : ℝ) * radius ^ power * ‖first - second‖ := by
  have derivative (value : ℂ) : HasDerivAt (fun current : ℂ => current ^ (power + 1))
      ((power + 1 : ℂ) * value ^ power) value := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one] using
      (hasDerivAt_id value).pow (power + 1)
  have bound (value : ℂ) (inside : value ∈ Metric.closedBall (0 : ℂ) radius) :
      ‖(power + 1 : ℂ) * value ^ power‖ ≤ (power + 1 : ℝ) * radius ^ power := by
    have small : ‖value‖ ≤ radius := by simpa only [Metric.mem_closedBall, dist_zero_right] using inside
    rw [norm_mul, norm_pow]
    have scalarNorm : ‖(power + 1 : ℂ)‖ = (power + 1 : ℝ) := by
      norm_cast
    rw [scalarNorm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) small power) (by positivity)
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun value (_ : value ∈ Metric.closedBall (0 : ℂ) radius) => (derivative value).hasDerivWithinAt)
    bound (convex_closedBall (0 : ℂ) radius)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using secondBound)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using firstBound)

theorem signedExteriorMoment_difference_norm_le (first second : FourPointConfiguration) (power : ℕ)
    {radius : ℝ} (nonnegative : 0 ≤ radius)
    (firstBound : ∀ patch, ‖first patch‖ ≤ radius) (secondBound : ∀ patch, ‖second patch‖ ≤ radius) :
    ‖signedExteriorMoment first power - signedExteriorMoment second power‖ ≤
      (power + 1 : ℝ) * radius ^ power * ‖first - second‖ := by
  rw [signedExteriorMoment, signedExteriorMoment, ← map_sub]
  apply (fourPointSignedAverageCLM_norm_le _).trans
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro patch
  have estimate := complex_power_difference_bound (star (first patch)) (star (second patch)) power nonnegative
    (by simpa only [norm_star] using firstBound patch) (by simpa only [norm_star] using secondBound patch)
  rw [← star_sub, norm_star] at estimate
  exact estimate.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm (first - second) patch) (by positivity))

theorem signedExteriorMoment_coefficient_difference_norm_le (first second : FourPointConfiguration)
    (firstCoefficient secondCoefficient : ℂ) (power : ℕ) {radius : ℝ} (nonnegative : 0 ≤ radius)
    (firstBound : ∀ patch, ‖first patch‖ ≤ radius) (secondBound : ∀ patch, ‖second patch‖ ≤ radius) :
    ‖firstCoefficient * signedExteriorMoment first power - secondCoefficient * signedExteriorMoment second power‖ ≤
      ‖firstCoefficient‖ * ((power + 1 : ℝ) * radius ^ power * ‖first - second‖) +
        ‖firstCoefficient - secondCoefficient‖ * radius ^ (power + 1) := by
  have identity : firstCoefficient * signedExteriorMoment first power - secondCoefficient * signedExteriorMoment second power =
      firstCoefficient * (signedExteriorMoment first power - signedExteriorMoment second power) +
        (firstCoefficient - secondCoefficient) * signedExteriorMoment second power := by ring
  rw [identity]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (signedExteriorMoment_difference_norm_le first second power nonnegative firstBound secondBound)
      (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (signedExteriorMoment_norm_le second power nonnegative secondBound) (norm_nonneg _))

end EulerNonuniqueness.Section6
