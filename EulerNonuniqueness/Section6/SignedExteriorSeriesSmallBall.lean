import EulerNonuniqueness.Section6.SignedExteriorSeriesRelative

noncomputable section

namespace EulerNonuniqueness.Section6

theorem shifted_linear_small_geometric_le_two (power : ℕ) {ratio : ℝ}
    (nonnegative : 0 ≤ ratio) (small : ratio ≤ 1 / 2) :
    (power + 2 : ℝ) * ratio ^ power ≤ 2 := by
  induction power with
  | zero => norm_num
  | succ power induction =>
    push_cast
    have comparison : (power + 3 : ℝ) * ratio ≤ power + 2 := by
      have naturalNonnegative : 0 ≤ (power : ℝ) := by positivity
      nlinarith [mul_nonneg naturalNonnegative (sub_nonneg.mpr small)]
    calc
      (power + 1 + 2 : ℝ) * ratio ^ (power + 1) = ((power + 3 : ℝ) * ratio) * ratio ^ power := by ring
      _ ≤ (power + 2 : ℝ) * ratio ^ power := mul_le_mul_of_nonneg_right comparison (pow_nonneg nonnegative _)
      _ ≤ 2 := induction

theorem signedExteriorSeries_relative_small_ball_le
    (first second : FourPointConfiguration) (firstCoefficient secondCoefficient : ℕ → ℂ)
    {firstValue secondValue : ℂ} {radius : ℝ} (nonnegative : 0 ≤ radius) (small : radius ≤ 1 / 2)
    (firstBound : ∀ patch, ‖first patch‖ ≤ radius) (secondBound : ∀ patch, ‖second patch‖ ≤ radius)
    (firstSeries : HasSum (fun power => firstCoefficient power * signedExteriorMoment first power) firstValue)
    (secondSeries : HasSum (fun power => secondCoefficient power * signedExteriorMoment second power) secondValue)
    (firstTail : Summable (fun power : ℕ => ‖firstCoefficient (power + 1)‖))
    (differenceTail : Summable (fun power : ℕ => ‖firstCoefficient (power + 1) - secondCoefficient (power + 1)‖)) :
    ‖firstValue - secondValue‖ ≤
      ‖firstCoefficient 0‖ * ‖fourPointSignedAverageCLM first - fourPointSignedAverageCLM second‖ +
      ‖firstCoefficient 0 - secondCoefficient 0‖ * ‖fourPointSignedAverageCLM second‖ +
      (2 * radius * ∑' power : ℕ, ‖firstCoefficient (power + 1)‖) * ‖first - second‖ +
      radius ^ 2 * ∑' power : ℕ, ‖firstCoefficient (power + 1) - secondCoefficient (power + 1)‖ := by
  have linearBound (power : ℕ) : (power + 2 : ℝ) * radius ^ (power + 1) ≤ 2 * radius := by
    have actual := mul_le_mul_of_nonneg_right (shifted_linear_small_geometric_le_two power nonnegative small) nonnegative
    simpa only [pow_succ, mul_assoc] using actual
  have quadraticBound (power : ℕ) : radius ^ (power + 2) ≤ radius ^ 2 := by
    rw [pow_add]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ nonnegative (by linarith : radius ≤ 1))
  have firstCost (power : ℕ) : ‖firstCoefficient (power + 1)‖ * ((power + 2 : ℝ) * radius ^ (power + 1)) ≤
      (2 * radius) * ‖firstCoefficient (power + 1)‖ := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (linearBound power) (norm_nonneg (firstCoefficient (power + 1)))
  have differenceCost (power : ℕ) : ‖firstCoefficient (power + 1) - secondCoefficient (power + 1)‖ * radius ^ (power + 2) ≤
      radius ^ 2 * ‖firstCoefficient (power + 1) - secondCoefficient (power + 1)‖ := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (quadraticBound power)
      (norm_nonneg (firstCoefficient (power + 1) - secondCoefficient (power + 1)))
  have firstCostSummable := Summable.of_nonneg_of_le (fun power => by positivity) firstCost (firstTail.mul_left (2 * radius))
  have differenceCostSummable := Summable.of_nonneg_of_le (fun power => by positivity) differenceCost (differenceTail.mul_left (radius ^ 2))
  have firstSum := firstCostSummable.tsum_le_tsum firstCost (firstTail.mul_left (2 * radius))
  have differenceSum := differenceCostSummable.tsum_le_tsum differenceCost (differenceTail.mul_left (radius ^ 2))
  rw [tsum_mul_left] at firstSum differenceSum
  have actual := signedExteriorSeries_relative_le first second firstCoefficient secondCoefficient nonnegative
    firstBound secondBound firstSeries secondSeries firstCostSummable differenceCostSummable
  exact actual.trans (add_le_add (add_le_add_left
    (mul_le_mul_of_nonneg_right firstSum (norm_nonneg (first - second))) _) differenceSum)

end EulerNonuniqueness.Section6
