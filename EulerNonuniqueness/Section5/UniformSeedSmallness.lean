import EulerNonuniqueness.Section5.Delay
import EulerNonuniqueness.Section1.ExternalFieldScaleBounds

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.seed_exact_exponential (scales : Scales) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : ℕ) :
    scales.seed index = (2 * Real.sqrt 3 / Real.sqrt 2 * scales.ratio ^ 2) *
      ((scales.location (index + 1))⁻¹ ^ 4 * Real.exp (-4 * scales.omega (index + 1) ^ scales.alpha)) := by
  have omegaNext : scales.omega (index + 1) = scales.omega index * scales.ratio := by
    simp only [Scales.omega, pow_succ]
    ring
  have lengthFourth : scales.length (index + 1) ^ 4 =
      Real.exp (-4 * scales.omega (index + 1) ^ scales.alpha) := by
    rw [show scales.length (index + 1) ^ 4 = (scales.length (index + 1) ^ 2) ^ 2 by ring,
      scales.length_sq, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [← lengthFourth, Scales.seed, scales.adjacent_location_distance, Scales.circulation, omegaNext]
  field_simp [(scales.omega_pos frequencyPositive ratioPositive index).ne', Real.pi_ne_zero,
    (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)).ne', (scales.location_pos (index + 1)).ne']
  ring

theorem Scales.seed_le_weighted_exponential_total (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (index : ℕ) :
    scales.seed index ≤ (2 * Real.sqrt 3 / Real.sqrt 2 * scales.ratio ^ 2) *
      ∑' next : ℕ, scales.omega next ^ (4 : ℝ) * Real.exp (-4 * scales.omega next ^ scales.alpha) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have inverseLocation : (scales.location (index + 1))⁻¹ ≤ scales.omega (index + 1) := by
    rw [scales.location_eq_inv_pow, inv_inv]
    exact (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ratioBound _).trans
      (le_mul_of_one_le_left (by positivity) frequencyBound)
  have powerBound := pow_le_pow_left₀ (inv_nonneg.mpr (scales.location_pos (index + 1)).le) inverseLocation 4
  have seriesSummable := scales.weighted_exponential_summable frequencyPositive
    (show 1 < scales.ratio by linarith) alphaPositive 4 (coefficient := 4) (by norm_num)
  have termBound := seriesSummable.le_tsum (index + 1) (fun next _ =>
    mul_nonneg (Real.rpow_nonneg (scales.omega_pos frequencyPositive ratioPositive next).le _) (Real.exp_pos _).le)
  rw [scales.seed_exact_exponential frequencyPositive ratioPositive]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (mul_le_mul_of_nonneg_right powerBound (Real.exp_pos _).le).trans
  rw [show scales.omega (index + 1) ^ (4 : ℝ) = scales.omega (index + 1) ^ (4 : ℕ) by
    exact Real.rpow_natCast _ 4] at termBound
  exact termBound

theorem Scales.eventually_seed_lt_one (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ, ({scales with frequency := frequency}).seed index < 1 := by
  have boundTendsto := (scales.weighted_exponential_total_tendsto_zero
    (show 1 < scales.ratio by linarith) alphaPositive 4 (coefficient := 4) (by norm_num)).const_mul
      (2 * Real.sqrt 3 / Real.sqrt 2 * scales.ratio ^ 2)
  simp only [mul_zero] at boundTendsto
  filter_upwards [eventually_ge_atTop (1 : ℝ), boundTendsto.eventually (eventually_lt_nhds zero_lt_one)]
    with frequency frequencyBound totalSmall index
  exact (Scales.seed_le_weighted_exponential_total {scales with frequency := frequency}
    frequencyBound ratioBound alphaPositive index).trans_lt totalSmall

end EulerNonuniqueness.Paper
