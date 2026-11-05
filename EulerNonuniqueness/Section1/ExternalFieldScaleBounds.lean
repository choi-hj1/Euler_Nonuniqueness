import EulerNonuniqueness.Section1.FrequencySeriesDecay

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.circulation_div_location_pow_bound (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (order index : ℕ) :
    scales.circulation index / scales.location index ^ order ≤
      2 * Real.pi * (scales.omega index ^ (order + 1) * Real.exp (-2 * scales.omega index ^ scales.alpha)) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have inverseLocation : (scales.location index)⁻¹ ≤ scales.omega index := by
    rw [scales.location_eq_inv_pow, inv_inv]
    exact (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ratioBound index).trans
      (le_mul_of_one_le_left (pow_nonneg ratioPositive.le index) frequencyBound)
  have powerBound := pow_le_pow_left₀ (inv_nonneg.mpr (scales.location_pos index).le) inverseLocation order
  have comparison := mul_le_mul_of_nonneg_left powerBound (scales.circulation_pos frequencyPositive ratioPositive index).le
  rw [Scales.circulation, scales.length_sq] at comparison
  rw [div_eq_mul_inv, ← inv_pow, Scales.circulation, scales.length_sq]
  calc
    _ ≤ (2 * Real.pi * scales.omega index * Real.exp (-2 * scales.omega index ^ scales.alpha)) *
        scales.omega index ^ order := comparison
    _ = _ := by rw [pow_succ]; ring

theorem Scales.circulation_location_summable (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (order : ℕ) :
    Summable (fun index : ℕ => scales.circulation (index + 1) / scales.location (index + 1) ^ order) := by
  have fullSummable := (scales.weighted_exponential_summable (zero_lt_one.trans_le frequencyBound)
    (show 1 < scales.ratio by linarith) alphaPositive ((order + 1 : ℕ) : ℝ) (show (0 : ℝ) < 2 by norm_num)).mul_left
      (2 * Real.pi)
  have shifted := fullSummable.comp_injective (show Function.Injective (fun index : ℕ => index + 1) from
    fun _ _ equality => Nat.add_right_cancel equality)
  apply Summable.of_norm_bounded _ shifted
  intro index
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    exact div_nonneg (scales.circulation_pos (zero_lt_one.trans_le frequencyBound) (by linarith) _).le
      (pow_nonneg (scales.location_pos (index + 1)).le order))]
  simpa only [Real.rpow_natCast] using scales.circulation_div_location_pow_bound frequencyBound ratioBound order (index + 1)

theorem Scales.circulation_location_total_tendsto_zero (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (order : ℕ) :
    Tendsto (fun frequency : ℝ => ∑' index : ℕ,
      ({scales with frequency := frequency}).circulation (index + 1) /
        ({scales with frequency := frequency}).location (index + 1) ^ order) atTop (𝓝 0) := by
  have boundTendsto := (scales.weighted_exponential_total_tendsto_zero
    (show 1 < scales.ratio by linarith) alphaPositive ((order + 1 : ℕ) : ℝ) (show (0 : ℝ) < 2 by norm_num)).const_mul
      (2 * Real.pi)
  simp only [mul_zero] at boundTendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds boundTendsto
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with frequency frequencyBound
    apply tsum_nonneg
    intro index
    exact div_nonneg
      (Scales.circulation_pos {scales with frequency := frequency} (zero_lt_one.trans_le frequencyBound) (by linarith) _).le
      (pow_nonneg (Scales.location_pos {scales with frequency := frequency} (index + 1)).le order)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with frequency frequencyBound
    let changed : Scales := {scales with frequency := frequency}
    have fullSummable := (changed.weighted_exponential_summable (zero_lt_one.trans_le frequencyBound)
      (show 1 < scales.ratio by linarith) alphaPositive ((order + 1 : ℕ) : ℝ) (show (0 : ℝ) < 2 by norm_num)).mul_left
        (2 * Real.pi)
    have comparison := Summable.tsum_le_tsum_of_inj (fun index : ℕ => index + 1)
      (show Function.Injective (fun index : ℕ => index + 1) from fun _ _ equality => Nat.add_right_cancel equality)
      (fun index _ => by
        have omegaPositive := changed.omega_pos (zero_lt_one.trans_le frequencyBound) (by linarith) index
        positivity)
      (fun index => by simpa only [Real.rpow_natCast] using
        changed.circulation_div_location_pow_bound frequencyBound ratioBound order (index + 1))
      (changed.circulation_location_summable frequencyBound ratioBound alphaPositive order) fullSummable
    simpa only [tsum_mul_left] using comparison

theorem Scales.strain_tendsto_zero (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) :
    Tendsto (fun frequency : ℝ => ({scales with frequency := frequency}).strain) atTop (𝓝 0) :=
  scales.circulation_location_total_tendsto_zero ratioBound alphaPositive 2

theorem Scales.hessian_tendsto_zero (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) :
    Tendsto (fun frequency : ℝ => ({scales with frequency := frequency}).hessian) atTop (𝓝 0) :=
  scales.circulation_location_total_tendsto_zero ratioBound alphaPositive 3

end EulerNonuniqueness.Paper
