import EulerNonuniqueness.General.LogPerturbation
import EulerNonuniqueness.Section6.IntegrableUnstableDuhamel

noncomputable section

namespace EulerNonuniqueness.Section6

theorem signed_exponential_exit_time_error {rate scale coefficient actualCoefficient threshold time error : ℝ}
    (ratePositive : 0 < rate) (scalePositive : 0 < scale) (coefficientPositive : 0 < coefficient)
    (thresholdPositive : 0 < threshold) (coefficientBound : |actualCoefficient - coefficient| ≤ error)
    (small : error ≤ coefficient / 2)
    (exitIdentity : scale * actualCoefficient * Real.exp (rate * time) = threshold) :
    |time - Real.log (threshold / (scale * coefficient)) / rate| ≤ 2 * error / (rate * coefficient) := by
  have actualPositive : 0 < actualCoefficient := by
    have lower := (abs_le.mp coefficientBound).1
    linarith
  have logarithmic := exponential_exit_time ratePositive (mul_pos scalePositive actualPositive) exitIdentity
  have differenceIdentity : time - Real.log (threshold / (scale * coefficient)) / rate =
      (Real.log coefficient - Real.log actualCoefficient) / rate := by
    rw [logarithmic, Real.log_div thresholdPositive.ne' (mul_pos scalePositive actualPositive).ne',
      Real.log_div thresholdPositive.ne' (mul_pos scalePositive coefficientPositive).ne',
      Real.log_mul scalePositive.ne' actualPositive.ne', Real.log_mul scalePositive.ne' coefficientPositive.ne']
    ring
  rw [differenceIdentity, abs_div, abs_of_pos ratePositive, abs_sub_comm]
  calc
    _ ≤ (2 * error / coefficient) / rate :=
      div_le_div_of_nonneg_right (abs_log_sub_log_le_of_relative_error coefficientPositive coefficientBound small) ratePositive.le
    _ = _ := by ring

theorem unstable_exit_time_error_of_weighted_bound {trajectory : ℝ → ℝ}
    {rate scale coefficient threshold time error : ℝ}
    (ratePositive : 0 < rate) (scalePositive : 0 < scale) (coefficientPositive : 0 < coefficient)
    (thresholdPositive : 0 < threshold) (exitIdentity : trajectory time = threshold)
    (weightedBound : |Real.exp (-rate * time) * trajectory time - scale * coefficient| ≤ scale * error)
    (small : error ≤ coefficient / 2) :
    |time - Real.log (threshold / (scale * coefficient)) / rate| ≤ 2 * error / (rate * coefficient) := by
  let actualCoefficient := Real.exp (-rate * time) * trajectory time / scale
  have coefficientBound : |actualCoefficient - coefficient| ≤ error := by
    have identity : actualCoefficient - coefficient =
        (Real.exp (-rate * time) * trajectory time - scale * coefficient) / scale := by
      dsimp only [actualCoefficient]
      field_simp
    rw [identity, abs_div, abs_of_pos scalePositive]
    exact (div_le_iff₀ scalePositive).mpr (by nlinarith)
  have identity : scale * actualCoefficient * Real.exp (rate * time) = threshold := by
    dsimp only [actualCoefficient]
    have cancellation : Real.exp (-rate * time) * Real.exp (rate * time) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    calc
      _ = trajectory time * (Real.exp (-rate * time) * Real.exp (rate * time)) := by
        field_simp
        ring
      _ = threshold := by rw [cancellation, mul_one, exitIdentity]
  exact signed_exponential_exit_time_error ratePositive scalePositive coefficientPositive thresholdPositive
    coefficientBound small identity

end EulerNonuniqueness.Section6
