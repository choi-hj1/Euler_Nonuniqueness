import EulerNonuniqueness.Section3.DiskForcingPrimitive
import EulerNonuniqueness.Section3.DiskForcingModeBounds

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem diskForcingPrimitive_polynomial_bound (degree : ℕ) {frequency : ℝ}
    (nonzero : frequency ≠ 0) (amplitude : ℝ → ℂ) (time : ℝ) :
    ‖diskForcingPrimitive degree frequency amplitude time‖ ≤
      (4 * ((degree + 1 : ℕ) : ℝ) / |frequency|) * ‖amplitude time‖ := by
  rw [diskForcingPrimitive_norm]
  have modeBound := (c1Conjugate_norm_bound (diskCircleMode (degree + 1))).trans (diskCircleMode_norm_bound degree)
  have frequencyPositive : 0 < |frequency| := abs_pos.mpr nonzero
  have degreePositive : (0 : ℝ) < ((degree + 1 : ℕ) : ℝ) := by positivity
  calc
    _ ≤ (2 / (((degree + 1 : ℕ) : ℝ) * |frequency|)) * ‖amplitude time‖ *
        (2 * (((degree + 1 : ℕ) : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left modeBound (by positivity)
    _ = _ := by field_simp; ring

theorem diskForcingPrimitive_weighted_bound (degree : ℕ) {frequency : ℝ}
    (nonzero : frequency ≠ 0) (amplitude : ℝ → ℂ) (time : ℝ) :
    ‖diskForcingPrimitive degree frequency amplitude time‖ ≤
      (4 / |frequency|) * ((2 : ℝ) ^ (degree + 1) * ‖amplitude time‖) := by
  apply (diskForcingPrimitive_polynomial_bound degree nonzero amplitude time).trans
  have degreeBound : ((degree + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (degree + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := degree + 1)).le
  have frequencyPositive : 0 < |frequency| := abs_pos.mpr nonzero
  have actual := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left degreeBound (show 0 ≤ 4 / |frequency| by positivity)) (norm_nonneg (amplitude time))
  convert actual using 1 <;> ring

end

end EulerNonuniqueness.Paper
