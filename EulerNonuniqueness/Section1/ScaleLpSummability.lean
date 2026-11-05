import EulerNonuniqueness.Section1.Scales

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.weighted_exponential_summable (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioGreaterOne : 1 < scales.ratio)
    (alphaPositive : 0 < scales.alpha) (power : ℝ) {coefficient : ℝ} (coefficientPositive : 0 < coefficient) :
    Summable (fun index : ℕ => scales.omega index ^ power *
      Real.exp (-coefficient * scales.omega index ^ scales.alpha)) := by
  have decay := (General.tendsto_rpow_mul_exp_neg_rpow (power + 1) scales.alpha coefficient
    alphaPositive coefficientPositive).comp (scales.omega_tendsto frequencyPositive ratioGreaterOne)
  have small := decay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  apply Summable.of_norm_bounded_eventually_nat (fun index => (scales.omega index)⁻¹)
    (scales.inverse_omega_summable ratioGreaterOne)
  filter_upwards [small] with index small
  dsimp only [Function.comp_def] at small
  have omegaPositive := scales.omega_pos frequencyPositive (zero_lt_one.trans ratioGreaterOne) index
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.rpow_pos_of_pos omegaPositive power) (Real.exp_pos _)),
    ← one_div]
  apply (le_div_iff₀ omegaPositive).mpr
  rw [Real.rpow_add omegaPositive, Real.rpow_one] at small
  convert small.le using 1
  ring

end EulerNonuniqueness.Paper
