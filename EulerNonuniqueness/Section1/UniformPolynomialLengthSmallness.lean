import EulerNonuniqueness.Section1.FrequencySeriesDecay

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_omega_pow_length_lt (scales : Scales)
    (ratioGreaterOne : 1 < scales.ratio) (alphaPositive : 0 < scales.alpha)
    (power : ℕ) {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      ({scales with frequency := frequency}).omega index ^ power *
        ({scales with frequency := frequency}).length index < tolerance := by
  have totalTendsto := scales.weighted_exponential_total_tendsto_zero ratioGreaterOne alphaPositive
    (power : ℝ) (coefficient := 1) zero_lt_one
  simp only [Real.rpow_natCast, one_mul, neg_mul] at totalTendsto
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    totalTendsto.eventually (eventually_lt_nhds tolerancePositive)] with frequency frequencyPositive totalSmall
  intro index
  let actual : Scales := {scales with frequency := frequency}
  have summable := actual.weighted_exponential_summable frequencyPositive ratioGreaterOne alphaPositive
    (power : ℝ) (coefficient := 1) zero_lt_one
  simp only [Real.rpow_natCast, one_mul, neg_mul] at summable
  have term := summable.le_tsum index (fun next _ =>
    mul_nonneg (pow_nonneg (actual.omega_pos frequencyPositive (zero_lt_one.trans ratioGreaterOne) next).le _)
      (Real.exp_pos _).le)
  exact term.trans_lt totalSmall

end EulerNonuniqueness.Paper
