import EulerNonuniqueness.Section1.ScaleLpSummability

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.weighted_exponential_frequency_bound (scales : Scales)
    (ratioGreaterOne : 1 < scales.ratio) (alphaPositive : 0 < scales.alpha)
    (power : ℝ) {coefficient frequency : ℝ} (coefficientPositive : 0 < coefficient)
    (frequencyBound : 1 ≤ frequency) (index : ℕ) :
    ({scales with frequency := frequency}).omega index ^ power *
        Real.exp (-coefficient * ({scales with frequency := frequency}).omega index ^ scales.alpha) ≤
      (frequency ^ power * Real.exp (-(coefficient / 2) * frequency ^ scales.alpha)) *
        (({scales with frequency := 1}).omega index ^ power *
          Real.exp (-(coefficient / 2) * ({scales with frequency := 1}).omega index ^ scales.alpha)) := by
  let unit : Scales := {scales with frequency := 1}
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyBound
  have unitPositive := unit.omega_pos zero_lt_one (zero_lt_one.trans ratioGreaterOne) index
  have unitLarge : 1 ≤ unit.omega index := by
    simpa only [unit, Scales.omega, one_mul] using one_le_pow₀ ratioGreaterOne.le (n := index)
  have frequencyPowerLarge : 1 ≤ frequency ^ scales.alpha := Real.one_le_rpow frequencyBound alphaPositive.le
  have unitPowerLarge : 1 ≤ unit.omega index ^ scales.alpha := Real.one_le_rpow unitLarge alphaPositive.le
  have productBound : frequency ^ scales.alpha + unit.omega index ^ scales.alpha ≤
      2 * (frequency ^ scales.alpha * unit.omega index ^ scales.alpha) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr frequencyPowerLarge) (sub_nonneg.mpr unitPowerLarge)]
  have omegaIdentity : ({scales with frequency := frequency}).omega index = frequency * unit.omega index := by
    simp only [Scales.omega, unit, one_mul]
  have exponentialBound : Real.exp (-coefficient * (frequency * unit.omega index) ^ scales.alpha) ≤
      Real.exp (-(coefficient / 2) * frequency ^ scales.alpha) *
        Real.exp (-(coefficient / 2) * unit.omega index ^ scales.alpha) := by
    rw [← Real.exp_add, Real.mul_rpow frequencyPositive.le unitPositive.le]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left productBound (show 0 ≤ coefficient / 2 by positivity)]
  rw [omegaIdentity, Real.mul_rpow frequencyPositive.le unitPositive.le]
  calc
    _ ≤ (frequency ^ power * unit.omega index ^ power) *
        (Real.exp (-(coefficient / 2) * frequency ^ scales.alpha) *
          Real.exp (-(coefficient / 2) * unit.omega index ^ scales.alpha)) :=
      mul_le_mul_of_nonneg_left exponentialBound (by positivity)
    _ = _ := by ring

theorem Scales.weighted_exponential_total_tendsto_zero (scales : Scales)
    (ratioGreaterOne : 1 < scales.ratio) (alphaPositive : 0 < scales.alpha)
    (power : ℝ) {coefficient : ℝ} (coefficientPositive : 0 < coefficient) :
    Tendsto (fun frequency : ℝ => ∑' index : ℕ,
      ({scales with frequency := frequency}).omega index ^ power *
        Real.exp (-coefficient * ({scales with frequency := frequency}).omega index ^ scales.alpha))
      atTop (𝓝 0) := by
  let unit : Scales := {scales with frequency := 1}
  let envelope := fun index : ℕ => unit.omega index ^ power *
    Real.exp (-(coefficient / 2) * unit.omega index ^ scales.alpha)
  have envelopeSummable : Summable envelope := unit.weighted_exponential_summable
    zero_lt_one ratioGreaterOne alphaPositive power (show 0 < coefficient / 2 by positivity)
  have boundTendsto := (EulerNonuniqueness.General.tendsto_rpow_mul_exp_neg_rpow power
    scales.alpha (coefficient / 2) alphaPositive (by positivity)).mul_const (∑' index, envelope index)
  simp only [zero_mul] at boundTendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds boundTendsto
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with frequency frequencyPositive
    apply tsum_nonneg
    intro index
    have omegaPositive := Scales.omega_pos {scales with frequency := frequency}
      frequencyPositive (zero_lt_one.trans ratioGreaterOne) index
    exact mul_nonneg (Real.rpow_nonneg omegaPositive.le _) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with frequency frequencyBound
    have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyBound
    have fullSummable := Scales.weighted_exponential_summable {scales with frequency := frequency}
      frequencyPositive ratioGreaterOne alphaPositive power coefficientPositive
    have comparison := Summable.tsum_le_tsum
      (fun index => scales.weighted_exponential_frequency_bound ratioGreaterOne alphaPositive power coefficientPositive frequencyBound index)
      fullSummable (envelopeSummable.mul_left (frequency ^ power * Real.exp (-(coefficient / 2) * frequency ^ scales.alpha)))
    simpa only [tsum_mul_left] using comparison

end EulerNonuniqueness.Paper
