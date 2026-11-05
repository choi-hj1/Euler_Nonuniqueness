import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

theorem stable_solution_eq_zero_of_tendsto_atBot
    {state remainder : ℝ → ℝ} {rate endpoint : ℝ}
    (ratePositive : 0 < rate) (continuous : ContinuousOn state (Iic endpoint))
    (equation : ∀ time < endpoint, HasDerivAt state (-rate * state time + remainder time) time)
    (errorBound : ∀ time < endpoint, |remainder time| ≤ (rate / 2) * |state time|)
    (limit : Tendsto state atBot (𝓝 0)) :
    ∀ time ≤ endpoint, state time = 0 := by
  let weighted := fun time => Real.exp (rate * time) * state time ^ 2
  have derivative (time : ℝ) (inside : time < endpoint) : HasDerivAt weighted
      (Real.exp (rate * time) * rate * state time ^ 2 +
        Real.exp (rate * time) * (2 * state time * (-rate * state time + remainder time))) time := by
    simpa [weighted] using (((hasDerivAt_id time).const_mul rate).exp).mul ((equation time inside).pow 2)
  have sign (time : ℝ) (inside : time < endpoint) :
      Real.exp (rate * time) * rate * state time ^ 2 +
        Real.exp (rate * time) * (2 * state time * (-rate * state time + remainder time)) ≤ 0 := by
    have product := mul_le_mul_of_nonneg_left (errorBound time inside) (abs_nonneg (state time))
    have signed := le_abs_self (state time * remainder time)
    rw [abs_mul] at signed
    have square : |state time| * |state time| = state time ^ 2 := by rw [← sq_abs]; ring
    have control : 2 * state time * remainder time ≤ rate * state time ^ 2 := by
      nlinarith
    nlinarith [mul_nonneg (Real.exp_pos (rate * time)).le
      (show 0 ≤ rate * state time ^ 2 - 2 * state time * remainder time by linarith)]
  have weightedContinuous : ContinuousOn weighted (Iic endpoint) := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul (continuous.pow 2)
  have decreasing : AntitoneOn weighted (Iic endpoint) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic endpoint) weightedContinuous
    · intro time member
      rw [interior_Iic] at member
      exact (derivative time member).differentiableAt.differentiableWithinAt
    · intro time member
      rw [interior_Iic] at member
      rw [(derivative time member).deriv]
      exact sign time member
  have weightedNonnegative (time : ℝ) : 0 ≤ weighted time := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have upper : ∀ᶠ time : ℝ in atBot, weighted time ≤ state time ^ 2 := by
    filter_upwards [eventually_le_atBot (0 : ℝ)] with time nonpositive
    exact mul_le_of_le_one_left (sq_nonneg _) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ratePositive.le nonpositive))
  have weightedLimit : Tendsto weighted atBot (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall weightedNonnegative) upper
    simpa using limit.pow 2
  intro time inside
  have nonpositive : weighted time ≤ 0 := by
    apply ge_of_tendsto weightedLimit
    filter_upwards [eventually_le_atBot time] with earlier before
    exact decreasing (before.trans inside) inside before
  have zero : weighted time = 0 := le_antisymm nonpositive (weightedNonnegative time)
  have squareZero : state time ^ 2 = 0 := (mul_eq_zero.mp zero).resolve_left (Real.exp_ne_zero _)
  exact sq_eq_zero_iff.mp squareZero

end EulerNonuniqueness.General
