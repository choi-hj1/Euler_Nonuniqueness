import EulerNonuniqueness.Section1.FrequencySeriesDecay
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.length_div_location_le_weighted_total (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (index : ℕ) :
    scales.length index / scales.location index ≤
      ∑' next : ℕ, scales.omega next * Real.exp (-scales.omega next ^ scales.alpha) := by
  have frequencyPositive := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have inverseLocation : (scales.location index)⁻¹ ≤ scales.omega index := by
    rw [scales.location_eq_inv_pow, inv_inv]
    exact (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ratioBound _).trans
      (le_mul_of_one_le_left (by positivity) frequencyBound)
  have summable := scales.weighted_exponential_summable frequencyPositive
    (show 1 < scales.ratio by linarith) alphaPositive 1 (coefficient := 1) zero_lt_one
  simp only [Real.rpow_one, one_mul, neg_mul] at summable
  have termBound := summable.le_tsum index (fun next _ =>
    mul_nonneg (scales.omega_pos frequencyPositive ratioPositive next).le (Real.exp_pos _).le)
  apply le_trans _ termBound
  rw [Scales.length, div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right inverseLocation (Real.exp_pos _).le

theorem Scales.eventually_length_lt_location (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      ({scales with frequency := frequency}).length index < tolerance * scales.location index := by
  have totalTendsto := scales.weighted_exponential_total_tendsto_zero
    (show 1 < scales.ratio by linarith) alphaPositive 1 (coefficient := 1) zero_lt_one
  simp only [Real.rpow_one, one_mul, neg_mul] at totalTendsto
  filter_upwards [eventually_ge_atTop (1 : ℝ), totalTendsto.eventually (eventually_lt_nhds tolerancePositive)]
    with frequency frequencyBound totalSmall index
  have estimate := (Scales.length_div_location_le_weighted_total {scales with frequency := frequency}
    frequencyBound ratioBound alphaPositive index).trans_lt totalSmall
  exact (div_lt_iff₀ (scales.location_pos index)).mp estimate

theorem Scales.radius_div_length_uniform_bound (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioBound : 1 ≤ scales.ratio) (index : ℕ) :
    scales.radius index / scales.length index ≤ Real.sqrt (2 / (scales.amplitude * scales.frequency ^ 3)) := by
  have ratioPositive := zero_lt_one.trans_le ratioBound
  have omegaBound := scales.omega_ge_frequency frequencyPositive ratioBound index
  have denominatorPositive : 0 < scales.amplitude * scales.frequency ^ 3 := by positivity
  apply Real.le_sqrt_of_sq_le
  have squareIdentity : (scales.radius index / scales.length index) ^ 2 =
      2 / (scales.amplitude * scales.omega index ^ 3) := by
    rw [div_pow, scales.radius_sq amplitudePositive frequencyPositive ratioPositive]
    field_simp [(scales.length_pos index).ne', amplitudePositive.ne',
      (scales.omega_pos frequencyPositive ratioPositive index).ne']
    ring
  rw [squareIdentity]
  exact div_le_div_of_nonneg_left (by norm_num) denominatorPositive
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ frequencyPositive.le omegaBound 3) amplitudePositive.le)

theorem Scales.eventually_radius_lt_length (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 1 ≤ scales.ratio)
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      ({scales with frequency := frequency}).radius index <
        tolerance * ({scales with frequency := frequency}).length index := by
  have powerTendsto := (tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 3
  have coefficientTendsto := powerTendsto.const_mul (2 / scales.amplitude)
  have sqrtTendsto := Real.continuous_sqrt.continuousAt.tendsto.comp coefficientTendsto
  have boundTendsto : Tendsto (fun frequency : ℝ => Real.sqrt (2 / (scales.amplitude * frequency ^ 3))) atTop (𝓝 0) := by
    convert sqrtTendsto using 1
    · ext frequency
      simp [div_eq_mul_inv, mul_inv_rev, inv_pow, mul_assoc, mul_comm, mul_left_comm]
    · simp
  filter_upwards [eventually_gt_atTop (0 : ℝ), boundTendsto.eventually (eventually_lt_nhds tolerancePositive)]
    with frequency frequencyPositive boundSmall index
  have estimate := (Scales.radius_div_length_uniform_bound {scales with frequency := frequency}
    amplitudePositive frequencyPositive ratioBound index).trans_lt boundSmall
  exact (div_lt_iff₀ (Scales.length_pos _ index)).mp estimate

end EulerNonuniqueness.Paper
