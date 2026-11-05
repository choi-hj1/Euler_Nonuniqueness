import EulerNonuniqueness.Section1.ExternalFieldScaleBounds
import EulerNonuniqueness.Section1.FrequencyPointDecay

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.omega_monotone (scales : Scales) (frequencyNonnegative : 0 ≤ scales.frequency)
    (ratioBound : 1 ≤ scales.ratio) : Monotone scales.omega := by
  intro first second ordered
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ratioBound ordered) frequencyNonnegative

theorem Scales.circulation_div_length_le (scales : Scales) (frequencyPositive : 0 < scales.frequency)
    (ratioBound : 1 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (receiver source : ℕ) (ordered : receiver ≤ source) :
    scales.circulation source / scales.length receiver ≤
      2 * Real.pi * scales.omega source * Real.exp (-scales.omega source ^ scales.alpha) := by
  have omegaBound := scales.omega_monotone frequencyPositive.le ratioBound ordered
  have powerBound := Real.rpow_le_rpow
    (scales.omega_pos frequencyPositive (zero_lt_one.trans_le ratioBound) receiver).le omegaBound alphaPositive.le
  have identity : scales.circulation source / scales.length receiver =
      2 * Real.pi * scales.omega source *
        Real.exp (-2 * scales.omega source ^ scales.alpha + scales.omega receiver ^ scales.alpha) := by
    rw [Scales.circulation, scales.length_sq, Scales.length, mul_div_assoc, ← Real.exp_sub]
    congr 2
    ring
  rw [identity]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (scales.omega_pos frequencyPositive (zero_lt_one.trans_le ratioBound) source).le)

theorem Scales.tail_circulation_div_length_one_le (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioGreaterOne : 1 < scales.ratio)
    (alphaPositive : 0 < scales.alpha) :
    (∑' index : ℕ, scales.circulation (index + 2)) / scales.length 1 ≤
      2 * Real.pi * ∑' index : ℕ,
        scales.omega index * Real.exp (-scales.omega index ^ scales.alpha) := by
  have fullSummable := (scales.weighted_exponential_summable frequencyPositive ratioGreaterOne alphaPositive
    1 (coefficient := 1) zero_lt_one).mul_left (2 * Real.pi)
  simp only [Real.rpow_one, one_mul, neg_mul] at fullSummable
  have shifted := fullSummable.comp_injective (show Function.Injective (fun index : ℕ => index + 2) from
    fun _ _ equality => Nat.add_right_cancel equality)
  have termBound (index : ℕ) : scales.circulation (index + 2) / scales.length 1 ≤
      2 * Real.pi * (scales.omega (index + 2) * Real.exp (-scales.omega (index + 2) ^ scales.alpha)) := by
    simpa only [mul_assoc] using scales.circulation_div_length_le frequencyPositive ratioGreaterOne.le alphaPositive 1
      (index + 2) (by omega)
  have dividedSummable : Summable (fun index : ℕ => scales.circulation (index + 2) / scales.length 1) := by
    apply Summable.of_norm_bounded _ shifted
    intro index
    rw [Real.norm_eq_abs, abs_of_pos (div_pos
      (scales.circulation_pos frequencyPositive (zero_lt_one.trans ratioGreaterOne) _) (scales.length_pos 1))]
    exact termBound index
  rw [← tsum_div_const]
  have comparison := Summable.tsum_le_tsum_of_inj (fun index : ℕ => index + 2)
    (show Function.Injective (fun index : ℕ => index + 2) from fun _ _ equality => Nat.add_right_cancel equality)
    (fun index _ => by
      have omegaPositive := scales.omega_pos frequencyPositive (zero_lt_one.trans ratioGreaterOne) index
      positivity) termBound dividedSummable fullSummable
  simpa only [tsum_mul_left] using comparison

theorem Scales.tail_circulation_div_length_one_tendsto_zero (scales : Scales)
    (ratioGreaterOne : 1 < scales.ratio) (alphaPositive : 0 < scales.alpha) :
    Tendsto (fun frequency : ℝ =>
      (∑' index : ℕ, ({scales with frequency := frequency}).circulation (index + 2)) /
        ({scales with frequency := frequency}).length 1) atTop (𝓝 0) := by
  have boundTendsto := (scales.weighted_exponential_total_tendsto_zero ratioGreaterOne alphaPositive
    1 (coefficient := 1) zero_lt_one).const_mul (2 * Real.pi)
  simp only [Real.rpow_one, one_mul, neg_mul, mul_zero] at boundTendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds boundTendsto
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with frequency frequencyPositive
    apply div_nonneg (tsum_nonneg (fun index =>
      (Scales.circulation_pos {scales with frequency := frequency} frequencyPositive (zero_lt_one.trans ratioGreaterOne) _).le))
      (Scales.length_pos _ _).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with frequency frequencyPositive
    exact Scales.tail_circulation_div_length_one_le {scales with frequency := frequency}
      frequencyPositive ratioGreaterOne alphaPositive

theorem Scales.outerDisplacementBound_tendsto_zero (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) :
    Tendsto (fun frequency : ℝ => ({scales with frequency := frequency}).outerDisplacementBound) atTop (𝓝 0) := by
  have ratioPositive : 0 < scales.ratio := by linarith
  have first := scales.tail_circulation_div_length_one_tendsto_zero (by linarith) alphaPositive
  have hessian := scales.hessian_tendsto_zero ratioBound alphaPositive
  have omegaLength := scales.omega_mul_length_frequency_tendsto_zero ratioPositive alphaPositive 1
  have length := scales.length_frequency_tendsto_zero ratioPositive alphaPositive 1
  have inversePower := (tendsto_inv_atTop_zero.comp (scales.omega_frequency_tendsto_atTop ratioPositive 1)).pow 4
  have combined := ((first.add (hessian.mul omegaLength)).add (hessian.mul length)).add inversePower
  simpa [Scales.outerDisplacementBound, Function.comp_def, mul_assoc] using combined

end EulerNonuniqueness.Paper
