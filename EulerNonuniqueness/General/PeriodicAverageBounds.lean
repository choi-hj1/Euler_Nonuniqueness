import Mathlib

open MeasureTheory Set

namespace EulerNonuniqueness.General

variable {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]

theorem periodic_average_norm_le {trajectory : ℝ → Value} {period bound : ℝ}
    (periodPositive : 0 < period) (continuous : Continuous trajectory)
    (bounded : ∀ time ∈ Icc 0 period, ‖trajectory time‖ ≤ bound) :
    ‖(1 / period : ℝ) • ∫ time in (0 : ℝ)..period, trajectory time‖ ≤ bound := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr periodPositive)]
  calc
    _ ≤ (1 / period) * ∫ time in (0 : ℝ)..period, ‖trajectory time‖ :=
      mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm periodPositive.le) (by positivity)
    _ ≤ (1 / period) * ∫ _time in (0 : ℝ)..period, bound := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact intervalIntegral.integral_mono_on periodPositive.le
        (continuous.norm.intervalIntegrable _ _) intervalIntegrable_const bounded
    _ = _ := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      field_simp

theorem periodic_weighted_average_norm_le {trajectory : ℝ → Value} {period bound : ℝ}
    (periodPositive : 0 < period) (continuous : Continuous trajectory)
    (bounded : ∀ time ∈ Icc 0 period, ‖trajectory time‖ ≤ bound) :
    ‖(1 / period : ℝ) • ∫ time in (0 : ℝ)..period, time • trajectory time‖ ≤ (period / 2) * bound := by
  have weightedContinuous : Continuous (fun time : ℝ => time • trajectory time) := continuous_id.smul continuous
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr periodPositive)]
  calc
    _ ≤ (1 / period) * ∫ time in (0 : ℝ)..period, ‖time • trajectory time‖ :=
      mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm periodPositive.le) (by positivity)
    _ ≤ (1 / period) * ∫ time in (0 : ℝ)..period, time * bound := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply intervalIntegral.integral_mono_on periodPositive.le (weightedContinuous.norm.intervalIntegrable _ _)
        ((continuous_id.mul continuous_const).intervalIntegrable _ _)
      intro time inside
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg inside.1]
      exact mul_le_mul_of_nonneg_left (bounded time inside) inside.1
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, integral_id]
      simp only [zero_pow (by decide : 2 ≠ 0), sub_zero]
      field_simp [periodPositive.ne']
      <;> ring

end EulerNonuniqueness.General
