import Mathlib

noncomputable section

namespace EulerNonuniqueness.Section6

theorem exponential_tail_at_threshold {rate scale amplitude threshold time : ℝ}
    (scaleNonnegative : 0 ≤ scale) (amplitudeNonnegative : 0 ≤ amplitude)
    (thresholdPositive : 0 < threshold)
    (growthBound : threshold ≤ scale * amplitude * Real.exp (rate * time)) :
    Real.exp (-(3 * rate / 4) * time) ≤ (amplitude / threshold) ^ (3 / 4 : ℝ) * scale ^ (3 / 4 : ℝ) := by
  have cancellation : Real.exp (rate * time) * Real.exp (-rate * time) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have reciprocalBound : Real.exp (-rate * time) ≤ scale * amplitude / threshold := by
    apply (le_div_iff₀ thresholdPositive).mpr
    have estimate := mul_le_mul_of_nonneg_right growthBound (Real.exp_pos (-rate * time)).le
    rw [mul_assoc (scale * amplitude), cancellation, mul_one] at estimate
    simpa only [mul_comm] using estimate
  have estimate := Real.rpow_le_rpow (Real.exp_pos (-rate * time)).le reciprocalBound
    (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have leftIdentity : Real.exp (-rate * time) ^ (3 / 4 : ℝ) = Real.exp (-(3 * rate / 4) * time) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have rightIdentity : (scale * amplitude / threshold) ^ (3 / 4 : ℝ) =
      (amplitude / threshold) ^ (3 / 4 : ℝ) * scale ^ (3 / 4 : ℝ) := by
    rw [show scale * amplitude / threshold = (amplitude / threshold) * scale by ring,
      Real.mul_rpow (div_nonneg amplitudeNonnegative thresholdPositive.le) scaleNonnegative]
  rwa [leftIdentity, rightIdentity] at estimate

end EulerNonuniqueness.Section6
