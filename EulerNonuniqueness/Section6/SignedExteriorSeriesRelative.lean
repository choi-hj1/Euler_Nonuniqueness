import EulerNonuniqueness.Section6.SignedExteriorMomentRelative

noncomputable section

namespace EulerNonuniqueness.Section6

theorem signedExteriorSeries_relative_le
    (first second : FourPointConfiguration) (firstCoefficient secondCoefficient : ℕ → ℂ)
    {firstValue secondValue : ℂ} {radius : ℝ} (nonnegative : 0 ≤ radius)
    (firstBound : ∀ patch, ‖first patch‖ ≤ radius) (secondBound : ∀ patch, ‖second patch‖ ≤ radius)
    (firstSeries : HasSum (fun power => firstCoefficient power * signedExteriorMoment first power) firstValue)
    (secondSeries : HasSum (fun power => secondCoefficient power * signedExteriorMoment second power) secondValue)
    (firstTail : Summable (fun power : ℕ => ‖firstCoefficient (power + 1)‖ *
      ((power + 2 : ℝ) * radius ^ (power + 1))))
    (differenceTail : Summable (fun power : ℕ =>
      ‖firstCoefficient (power + 1) - secondCoefficient (power + 1)‖ * radius ^ (power + 2))) :
    ‖firstValue - secondValue‖ ≤
      ‖firstCoefficient 0‖ * ‖fourPointSignedAverageCLM first - fourPointSignedAverageCLM second‖ +
      ‖firstCoefficient 0 - secondCoefficient 0‖ * ‖fourPointSignedAverageCLM second‖ +
      (∑' power : ℕ, ‖firstCoefficient (power + 1)‖ * ((power + 2 : ℝ) * radius ^ (power + 1))) * ‖first - second‖ +
      ∑' power : ℕ, ‖firstCoefficient (power + 1) - secondCoefficient (power + 1)‖ * radius ^ (power + 2) := by
  let head := firstCoefficient 0 * signedExteriorMoment first 0 - secondCoefficient 0 * signedExteriorMoment second 0
  have tail : HasSum (fun power : ℕ => firstCoefficient (power + 1) * signedExteriorMoment first (power + 1) -
      secondCoefficient (power + 1) * signedExteriorMoment second (power + 1)) (firstValue - secondValue - head) := by
    have actual := (hasSum_nat_add_iff' 1).mpr (firstSeries.sub secondSeries)
    simpa only [Finset.sum_range_one, head] using actual
  have costSeries := (firstTail.hasSum.mul_right ‖first - second‖).add differenceTail.hasSum
  have tailBound := tail.norm_le_of_bounded costSeries (fun power => by
    have actual := signedExteriorMoment_coefficient_difference_norm_le first second
      (firstCoefficient (power + 1)) (secondCoefficient (power + 1)) (power + 1) nonnegative firstBound secondBound
    convert actual using 1 <;> push_cast <;> ring)
  have headIdentity : head = firstCoefficient 0 * star (fourPointSignedAverageCLM first - fourPointSignedAverageCLM second) +
      (firstCoefficient 0 - secondCoefficient 0) * star (fourPointSignedAverageCLM second) := by
    simp only [head, signedExteriorMoment_zero, star_sub]
    ring
  have headBound : ‖head‖ ≤
      ‖firstCoefficient 0‖ * ‖fourPointSignedAverageCLM first - fourPointSignedAverageCLM second‖ +
      ‖firstCoefficient 0 - secondCoefficient 0‖ * ‖fourPointSignedAverageCLM second‖ := by
    rw [headIdentity]
    simpa only [norm_mul, norm_star] using norm_add_le
      (firstCoefficient 0 * star (fourPointSignedAverageCLM first - fourPointSignedAverageCLM second))
      ((firstCoefficient 0 - secondCoefficient 0) * star (fourPointSignedAverageCLM second))
  have triangle := norm_add_le head (firstValue - secondValue - head)
  rw [add_sub_cancel] at triangle
  exact triangle.trans ((add_le_add headBound tailBound).trans_eq (by ring))

end EulerNonuniqueness.Section6
