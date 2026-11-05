import EulerNonuniqueness.Section1.Scales

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.adjacent_return_frequency_gain_le (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioBound : 2 ≤ scales.ratio) (index : ℕ) :
    1 / (scales.omega index * scales.location (index + 1)) ≤ 2 / scales.frequency := by
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  have powerBound := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ratioBound index
  have identity : 1 / (scales.omega index * scales.location (index + 1)) =
      2 * (2 : ℝ) ^ index / (scales.frequency * scales.ratio ^ index) := by
    rw [Scales.omega, scales.location_eq_inv_pow, pow_succ]
    field_simp
    ring
  rw [identity]
  apply (div_le_div_iff₀ (mul_pos frequencyPositive (pow_pos ratioPositive index)) frequencyPositive).mpr
  have multiplied := mul_le_mul_of_nonneg_left powerBound frequencyPositive.le
  nlinarith only [multiplied]

theorem Scales.eventually_adjacent_return_frequency_gain_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      1 / (({scales with frequency := frequency}).omega index * scales.location (index + 1)) < tolerance := by
  have decay := (tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).const_mul 2
  simp only [mul_zero] at decay
  filter_upwards [eventually_gt_atTop (0 : ℝ), decay.eventually (eventually_lt_nhds tolerancePositive)]
    with frequency frequencyPositive small index
  have bound := (Scales.adjacent_return_frequency_gain_le {scales with frequency := frequency}
    frequencyPositive ratioBound index)
  exact bound.trans_lt (by simpa only [div_eq_mul_inv] using small)

end EulerNonuniqueness.Paper
