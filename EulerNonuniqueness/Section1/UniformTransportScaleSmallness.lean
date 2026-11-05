import EulerNonuniqueness.Section1.UniformInitialScaleSmallness

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.omega_length_div_location_le_weighted_total (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (index : ℕ) :
    scales.omega index * scales.length index / scales.location index ≤
      ∑' next : ℕ, scales.omega next ^ 2 * Real.exp (-scales.omega next ^ scales.alpha) := by
  have frequencyPositive := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have inverseLocation : (scales.location index)⁻¹ ≤ scales.omega index := by
    rw [scales.location_eq_inv_pow, inv_inv]
    exact (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ratioBound _).trans
      (le_mul_of_one_le_left (by positivity) frequencyBound)
  have summable := scales.weighted_exponential_summable frequencyPositive
    (show 1 < scales.ratio by linarith) alphaPositive 2 (coefficient := 1) zero_lt_one
  simp only [Real.rpow_two, one_mul, neg_mul] at summable
  have termBound := summable.le_tsum index (fun next _ =>
    mul_nonneg (sq_nonneg (scales.omega next)) (Real.exp_pos _).le)
  apply le_trans _ termBound
  rw [Scales.length, div_eq_mul_inv]
  calc
    _ = (scales.omega index * Real.exp (-scales.omega index ^ scales.alpha)) *
        (scales.location index)⁻¹ := rfl
    _ ≤ (scales.omega index * Real.exp (-scales.omega index ^ scales.alpha)) *
        scales.omega index := mul_le_mul_of_nonneg_left inverseLocation
          (mul_nonneg (scales.omega_pos frequencyPositive ratioPositive index).le (Real.exp_pos _).le)
    _ = _ := by ring

theorem Scales.eventually_omega_length_lt_location (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      ({scales with frequency := frequency}).omega index * ({scales with frequency := frequency}).length index <
        tolerance * scales.location index := by
  have totalTendsto := scales.weighted_exponential_total_tendsto_zero
    (show 1 < scales.ratio by linarith) alphaPositive 2 (coefficient := 1) zero_lt_one
  simp only [Real.rpow_two, one_mul, neg_mul] at totalTendsto
  filter_upwards [eventually_ge_atTop (1 : ℝ), totalTendsto.eventually (eventually_lt_nhds tolerancePositive)]
    with frequency frequencyBound totalSmall index
  have estimate := (Scales.omega_length_div_location_le_weighted_total {scales with frequency := frequency}
    frequencyBound ratioBound alphaPositive index).trans_lt totalSmall
  exact (div_lt_iff₀ (scales.location_pos index)).mp estimate

end EulerNonuniqueness.Paper
