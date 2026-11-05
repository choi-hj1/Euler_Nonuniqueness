import EulerNonuniqueness.Section6.LaplaceMomentErrorBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem exponential_constant_history_integral_bound {rate constant time : ℝ}
    (rateNonnegative : 0 ≤ rate) (constantNonnegative : 0 ≤ constant) (timeNonnegative : 0 ≤ time) :
    (∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * constant) ≤ constant * time := by
  have integrable : IntervalIntegrable (fun current => Real.exp (-rate * current) * constant) volume 0 time := by
    apply Continuous.intervalIntegrable
    fun_prop
  have estimate := intervalIntegral.integral_mono_on timeNonnegative integrable
    (continuous_const.intervalIntegrable 0 time) (fun current member =>
      mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by nlinarith [member.1])) constantNonnegative)
  simpa only [one_mul, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm time] using estimate

theorem laplace_exponential_affine_norm_bound {error : ℝ → ℂ}
    {decay growth slope constant horizon : ℝ}
    (continuous : Continuous error) (gapPositive : 0 < decay - growth)
    (slopeNonnegative : 0 ≤ slope) (constantNonnegative : 0 ≤ constant) (horizonNonnegative : 0 ≤ horizon)
    (bound : ∀ time ∈ Icc 0 horizon,
      ‖error time‖ ≤ Real.exp (growth * time) * (slope * time + constant)) :
    (∫ time in (0 : ℝ)..horizon, Real.exp (-decay * time) * ‖error time‖) ≤
      slope / (decay - growth) ^ 2 + constant / (decay - growth) := by
  have firstIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * ‖error time‖) volume 0 horizon :=
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous.norm)).intervalIntegrable _ _
  have secondIntegrable : IntervalIntegrable (fun time => Real.exp (-(decay - growth) * time) *
      (slope * time + constant)) volume 0 horizon := by
    apply Continuous.intervalIntegrable
    fun_prop
  apply (intervalIntegral.integral_mono_on horizonNonnegative firstIntegrable secondIntegrable ?_).trans
    (laplace_affine_integral_bound gapPositive slopeNonnegative constantNonnegative horizonNonnegative)
  intro time member
  have estimate := mul_le_mul_of_nonneg_left (bound time member) (Real.exp_pos (-decay * time)).le
  have identity : Real.exp (-decay * time) * (Real.exp (growth * time) * (slope * time + constant)) =
      Real.exp (-(decay - growth) * time) * (slope * time + constant) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  exact estimate.trans_eq identity

end EulerNonuniqueness.Section6
