import EulerNonuniqueness.Section6.SignedExteriorSeriesSmallBall

noncomputable section

namespace EulerNonuniqueness.Section6

theorem complexExteriorSeries_norm_le (point : ℂ) (coefficient : ℕ → ℂ) {value : ℂ} {radius : ℝ}
    (nonnegative : 0 ≤ radius) (small : radius ≤ 1) (pointBound : ‖point‖ ≤ radius)
    (series : HasSum (fun power : ℕ => coefficient power * star point ^ (power + 1)) value)
    (coefficientSummable : Summable (fun power => ‖coefficient power‖)) :
    ‖value‖ ≤ radius * ∑' power, ‖coefficient power‖ := by
  apply series.norm_le_of_bounded (coefficientSummable.hasSum.mul_left radius)
  intro power
  rw [norm_mul, norm_pow, norm_star]
  have powerBound : ‖point‖ ^ (power + 1) ≤ radius := by
    rw [pow_succ]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (pointBound.trans small))).trans pointBound
  exact (mul_le_mul_of_nonneg_left powerBound (norm_nonneg _)).trans_eq (by ring)

theorem complexExteriorSeries_relative_small_ball_le (first second : ℂ)
    (firstCoefficient secondCoefficient : ℕ → ℂ) {firstValue secondValue : ℂ} {radius : ℝ}
    (nonnegative : 0 ≤ radius) (small : radius ≤ 1 / 2) (firstBound : ‖first‖ ≤ radius) (secondBound : ‖second‖ ≤ radius)
    (firstSeries : HasSum (fun power : ℕ => firstCoefficient power * star first ^ (power + 1)) firstValue)
    (secondSeries : HasSum (fun power : ℕ => secondCoefficient power * star second ^ (power + 1)) secondValue)
    (firstSummable : Summable (fun power => ‖firstCoefficient power‖))
    (differenceSummable : Summable (fun power => ‖firstCoefficient power - secondCoefficient power‖)) :
    ‖firstValue - secondValue‖ ≤
      2 * (∑' power, ‖firstCoefficient power‖) * ‖first - second‖ +
        radius * ∑' power, ‖firstCoefficient power - secondCoefficient power‖ := by
  have costSeries := (firstSummable.hasSum.mul_right (2 * ‖first - second‖)).add
    (differenceSummable.hasSum.mul_left radius)
  have actual := (firstSeries.sub secondSeries).norm_le_of_bounded costSeries (fun power => by
    have identity : firstCoefficient power * star first ^ (power + 1) - secondCoefficient power * star second ^ (power + 1) =
        firstCoefficient power * (star first ^ (power + 1) - star second ^ (power + 1)) +
          (firstCoefficient power - secondCoefficient power) * star second ^ (power + 1) := by ring
    rw [identity]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul, norm_pow, norm_star]
    have difference := complex_power_difference_bound (star first) (star second) power nonnegative
      (by simpa only [norm_star] using firstBound) (by simpa only [norm_star] using secondBound)
    rw [← star_sub, norm_star] at difference
    have degreeBound : (power + 1 : ℝ) * radius ^ power ≤ 2 := by
      exact (mul_le_mul_of_nonneg_right (by norm_num : (power + 1 : ℝ) ≤ power + 2)
        (pow_nonneg nonnegative _)).trans (shifted_linear_small_geometric_le_two power nonnegative small)
    have differenceBound := difference.trans (mul_le_mul_of_nonneg_right degreeBound (norm_nonneg _))
    have powerBound : ‖second‖ ^ (power + 1) ≤ radius := by
      rw [pow_succ]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (secondBound.trans (by linarith : radius ≤ 1)))).trans secondBound
    exact (add_le_add (mul_le_mul_of_nonneg_left differenceBound (norm_nonneg _))
      (mul_le_mul_of_nonneg_left powerBound (norm_nonneg _))).trans_eq (by ring))
  exact actual.trans_eq (by ring)

end EulerNonuniqueness.Section6
