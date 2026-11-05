import Mathlib

noncomputable section

namespace EulerNonuniqueness.Section6

theorem delay_exponential_endpoint {rate scale cutoff : ℝ}
    (rateNonzero : rate ≠ 0) (scalePositive : 0 < scale) (cutoffPositive : 0 < cutoff) :
    scale * Real.exp (rate * (Real.log (cutoff / scale) / rate)) = cutoff := by
  rw [mul_div_cancel₀ _ rateNonzero, Real.exp_log (div_pos cutoffPositive scalePositive)]
  field_simp

theorem delay_slow_exponential_bound {rate slowRate scale cutoff : ℝ}
    (ratePositive : 0 < rate) (scalePositive : 0 < scale) (scaleBound : scale ≤ 1)
    (cutoffPositive : 0 < cutoff) (slowRateBound : slowRate ≤ rate / 4) :
    scale * Real.exp (slowRate * (Real.log (cutoff / scale) / rate)) ≤
      cutoff ^ (slowRate / rate) * scale ^ (3 / 4 : ℝ) := by
  have identity : scale * Real.exp (slowRate * (Real.log (cutoff / scale) / rate)) =
      cutoff ^ (slowRate / rate) * scale ^ (1 - slowRate / rate) := by
    calc
      _ = Real.exp (Real.log scale) * Real.exp (slowRate * (Real.log (cutoff / scale) / rate)) := by rw [Real.exp_log scalePositive]
      _ = Real.exp (Real.log scale + slowRate * (Real.log (cutoff / scale) / rate)) := by rw [Real.exp_add]
      _ = Real.exp (Real.log cutoff * (slowRate / rate)) * Real.exp (Real.log scale * (1 - slowRate / rate)) := by
        rw [← Real.exp_add, Real.log_div cutoffPositive.ne' scalePositive.ne']
        congr 1
        ring
      _ = _ := by rw [Real.rpow_def_of_pos cutoffPositive, Real.rpow_def_of_pos scalePositive]
  rw [identity]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg cutoffPositive.le _)
  apply Real.rpow_le_rpow_of_exponent_ge scalePositive scaleBound
  have ratioBound : slowRate / rate ≤ (1 / 4 : ℝ) :=
    (div_le_iff₀ ratePositive).mpr (by nlinarith)
  linarith

end EulerNonuniqueness.Section6
