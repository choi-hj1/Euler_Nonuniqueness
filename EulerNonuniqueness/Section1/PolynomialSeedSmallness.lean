import EulerNonuniqueness.Section5.UniformSeedSmallness

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_polynomial_seed_rpow_lt (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (power : ℕ) {exponent tolerance : ℝ}
    (exponentPositive : 0 < exponent) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      let changed : Scales := {scales with frequency := frequency}
      changed.omega index ^ power * changed.seed index ^ exponent < tolerance := by
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  let constant : ℝ := 2 * Real.sqrt 3 / Real.sqrt 2 * scales.ratio ^ 2
  have constantPositive : 0 < constant := by dsimp only [constant]; positivity
  have decay := (EulerNonuniqueness.General.tendsto_rpow_mul_exp_neg_rpow
    ((power : ℝ) + 4 * exponent) scales.alpha (4 * exponent) alphaPositive
    (by positivity)).const_mul (constant ^ exponent)
  simp only [mul_zero] at decay
  obtain ⟨lower, small⟩ := (decay.eventually
    (eventually_lt_nhds tolerancePositive)).exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop (max 1 lower)] with frequency frequencyBound index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have frequencyOne : 1 ≤ changed.frequency := (le_max_left _ _).trans frequencyBound
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaPositive (next : ℕ) : 0 < changed.omega next :=
    changed.omega_pos frequencyPositive ratioPositive next
  have omegaNext : changed.omega index ≤ changed.omega (index + 1) := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by change 1 ≤ scales.ratio; linarith only [ratioBound]) (Nat.le_succ index))
      frequencyPositive.le
  have omegaLarge : lower ≤ changed.omega (index + 1) := by
    have frequencyLarge : lower ≤ changed.frequency := (le_max_right _ _).trans frequencyBound
    exact frequencyLarge.trans (le_mul_of_one_le_right frequencyPositive.le
      (one_le_pow₀ (by change 1 ≤ scales.ratio; linarith only [ratioBound])))
  have inverseLocation : (changed.location (index + 1))⁻¹ ≤ changed.omega (index + 1) := by
    rw [changed.location_eq_inv_pow, inv_inv]
    exact (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ratioBound _).trans
      (le_mul_of_one_le_left (by positivity) frequencyOne)
  have inversePower := pow_le_pow_left₀
    (inv_nonneg.mpr (changed.location_pos (index + 1)).le) inverseLocation 4
  have seedBound : changed.seed index ≤ constant *
      (changed.omega (index + 1) ^ 4 * Real.exp (-4 * changed.omega (index + 1) ^ changed.alpha)) := by
    rw [changed.seed_exact_exponential frequencyPositive ratioPositive]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right inversePower (Real.exp_pos _).le) constantPositive.le
  have seedPower := Real.rpow_le_rpow
    (changed.seed_pos frequencyPositive ratioPositive index).le seedBound exponentPositive.le
  have polynomial := pow_le_pow_left₀ (omegaPositive index).le omegaNext power
  have comparison := mul_le_mul polynomial seedPower
    (Real.rpow_nonneg (changed.seed_pos frequencyPositive ratioPositive index).le exponent)
    (pow_nonneg (omegaPositive (index + 1)).le power)
  have identity : changed.omega (index + 1) ^ power *
      (constant * (changed.omega (index + 1) ^ 4 *
        Real.exp (-4 * changed.omega (index + 1) ^ changed.alpha))) ^ exponent =
      constant ^ exponent * (changed.omega (index + 1) ^ ((power : ℝ) + 4 * exponent) *
        Real.exp (-(4 * exponent) * changed.omega (index + 1) ^ changed.alpha)) := by
    rw [Real.mul_rpow constantPositive.le (by positivity),
      Real.mul_rpow (pow_nonneg (omegaPositive (index + 1)).le 4) (Real.exp_pos _).le,
      ← Real.exp_mul, ← Real.rpow_natCast (changed.omega (index + 1)) power,
      ← Real.rpow_natCast (changed.omega (index + 1)) 4,
      ← Real.rpow_mul (omegaPositive (index + 1)).le]
    rw [show (-4 * changed.omega (index + 1) ^ changed.alpha) * exponent =
      -(4 * exponent) * changed.omega (index + 1) ^ changed.alpha by ring]
    rw [Real.rpow_add (omegaPositive (index + 1))]
    ring_nf
  exact (comparison.trans_eq identity).trans_lt (small _ omegaLarge)

end EulerNonuniqueness.Paper
