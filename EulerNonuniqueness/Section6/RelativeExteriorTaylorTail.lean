import EulerNonuniqueness.Section6.SignedExteriorSeriesSmallBall

noncomputable section

namespace EulerNonuniqueness.Section6

theorem complex_power_coefficient_difference_bound (first second firstCoefficient secondCoefficient : ℂ)
    (power : ℕ) {radius : ℝ} (nonnegative : 0 ≤ radius)
    (firstBound : ‖first‖ ≤ radius) (secondBound : ‖second‖ ≤ radius) :
    ‖firstCoefficient * (star first) ^ (power + 1) - secondCoefficient * (star second) ^ (power + 1)‖ ≤
      ‖firstCoefficient‖ * ((power + 1 : ℝ) * radius ^ power * ‖first - second‖) +
        ‖firstCoefficient - secondCoefficient‖ * radius ^ (power + 1) := by
  have identity : firstCoefficient * (star first) ^ (power + 1) - secondCoefficient * (star second) ^ (power + 1) =
      firstCoefficient * ((star first) ^ (power + 1) - (star second) ^ (power + 1)) +
        (firstCoefficient - secondCoefficient) * (star second) ^ (power + 1) := by ring
  rw [identity]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, norm_pow, norm_star]
  have difference := complex_power_difference_bound (star first) (star second) power nonnegative
    (by simpa only [norm_star] using firstBound) (by simpa only [norm_star] using secondBound)
  rw [← star_sub, norm_star] at difference
  exact add_le_add (mul_le_mul_of_nonneg_left difference (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) secondBound (power + 1)) (norm_nonneg _))

theorem antilinear_series_relative_tail_bound (first second : ℂ) (firstCoefficient secondCoefficient : ℕ → ℂ)
    {firstValue secondValue : ℂ} {radius : ℝ} (nonnegative : 0 ≤ radius) (small : radius ≤ 1 / 2)
    (firstBound : ‖first‖ ≤ radius) (secondBound : ‖second‖ ≤ radius)
    (firstSeries : HasSum (fun power => firstCoefficient power * (star first) ^ (power + 1)) firstValue)
    (secondSeries : HasSum (fun power => secondCoefficient power * (star second) ^ (power + 1)) secondValue)
    (firstTail : Summable (fun power : ℕ => ‖firstCoefficient (power + 1)‖))
    (differenceTail : Summable (fun power : ℕ => ‖firstCoefficient (power + 1) - secondCoefficient (power + 1)‖)) :
    ‖(firstValue - firstCoefficient 0 * star first) - (secondValue - secondCoefficient 0 * star second)‖ ≤
      (2 * radius * ∑' power : ℕ, ‖firstCoefficient (power + 1)‖) * ‖first - second‖ +
        radius ^ 2 * ∑' power : ℕ, ‖firstCoefficient (power + 1) - secondCoefficient (power + 1)‖ := by
  have tail : HasSum (fun power : ℕ => firstCoefficient (power + 1) * (star first) ^ (power + 2) -
      secondCoefficient (power + 1) * (star second) ^ (power + 2))
      ((firstValue - firstCoefficient 0 * star first) - (secondValue - secondCoefficient 0 * star second)) := by
    have actual := (hasSum_nat_add_iff' 1).mpr (firstSeries.sub secondSeries)
    convert actual using 1 <;> simp only [Finset.sum_range_one, zero_add, pow_one] <;> abel
  have linearBound (power : ℕ) : (power + 2 : ℝ) * radius ^ (power + 1) ≤ 2 * radius := by
    have actual := mul_le_mul_of_nonneg_right (shifted_linear_small_geometric_le_two power nonnegative small) nonnegative
    simpa only [pow_succ, mul_assoc] using actual
  have quadraticBound (power : ℕ) : radius ^ (power + 2) ≤ radius ^ 2 := by
    rw [pow_add]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ nonnegative (by linarith : radius ≤ 1))
  have costSeries := ((firstTail.hasSum.mul_left (2 * radius)).mul_right ‖first - second‖).add
    (differenceTail.hasSum.mul_left (radius ^ 2))
  simp only [tsum_mul_left] at costSeries
  exact tail.norm_le_of_bounded costSeries (fun power => by
    have bound := complex_power_coefficient_difference_bound first second (firstCoefficient (power + 1))
      (secondCoefficient (power + 1)) (power + 1) nonnegative firstBound secondBound
    have linear := mul_le_mul_of_nonneg_left (linearBound power) (norm_nonneg (firstCoefficient (power + 1)))
    have quadratic := mul_le_mul_of_nonneg_left (quadraticBound power)
      (norm_nonneg (firstCoefficient (power + 1) - secondCoefficient (power + 1)))
    apply bound.trans
    convert add_le_add (mul_le_mul_of_nonneg_right linear (norm_nonneg (first - second))) quadratic using 1 <;>
      push_cast <;> ring)

end EulerNonuniqueness.Section6
