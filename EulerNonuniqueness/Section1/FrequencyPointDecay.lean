import EulerNonuniqueness.Section1.FrequencySeriesDecay

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.omega_frequency_tendsto_atTop (scales : Scales)
    (ratioPositive : 0 < scales.ratio) (index : ℕ) :
    Tendsto (fun frequency : ℝ => ({scales with frequency := frequency}).omega index) atTop atTop := by
  simpa only [Scales.omega, mul_comm] using
    (tendsto_id : Tendsto (fun value : ℝ => value) atTop atTop).const_mul_atTop (pow_pos ratioPositive index)

theorem Scales.weighted_exponential_point_tendsto_zero (scales : Scales)
    (ratioPositive : 0 < scales.ratio) (alphaPositive : 0 < scales.alpha)
    (index : ℕ) (power : ℝ) {coefficient : ℝ} (coefficientPositive : 0 < coefficient) :
    Tendsto (fun frequency : ℝ => ({scales with frequency := frequency}).omega index ^ power *
      Real.exp (-coefficient * ({scales with frequency := frequency}).omega index ^ scales.alpha)) atTop (𝓝 0) :=
  (EulerNonuniqueness.General.tendsto_rpow_mul_exp_neg_rpow power scales.alpha coefficient
    alphaPositive coefficientPositive).comp (scales.omega_frequency_tendsto_atTop ratioPositive index)

theorem Scales.length_frequency_tendsto_zero (scales : Scales)
    (ratioPositive : 0 < scales.ratio) (alphaPositive : 0 < scales.alpha) (index : ℕ) :
    Tendsto (fun frequency : ℝ => ({scales with frequency := frequency}).length index) atTop (𝓝 0) := by
  simpa only [Real.rpow_zero, one_mul, neg_mul, Scales.length] using
    scales.weighted_exponential_point_tendsto_zero ratioPositive alphaPositive index 0 (coefficient := 1) zero_lt_one

theorem Scales.omega_mul_length_frequency_tendsto_zero (scales : Scales)
    (ratioPositive : 0 < scales.ratio) (alphaPositive : 0 < scales.alpha) (index : ℕ) :
    Tendsto (fun frequency : ℝ => ({scales with frequency := frequency}).omega index *
      ({scales with frequency := frequency}).length index) atTop (𝓝 0) := by
  simpa only [Real.rpow_one, one_mul, neg_mul, Scales.length] using
    scales.weighted_exponential_point_tendsto_zero ratioPositive alphaPositive index 1 (coefficient := 1) zero_lt_one

end EulerNonuniqueness.Paper
