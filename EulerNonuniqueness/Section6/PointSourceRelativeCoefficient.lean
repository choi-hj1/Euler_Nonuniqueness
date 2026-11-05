import EulerNonuniqueness.Section6.FourPointInversePowerRelative

noncomputable section

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 1000000

def pointSourceTaylorCoefficient (circulation receiverRadius : ℝ) (positions : FourPointConfiguration)
    (displacement : ℂ) (power : ℕ) : ℂ :=
  ((-1 : ℂ) ^ (power + 1) * Complex.I * (receiverRadius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)) *
    (circulation • ∑ patch : Fin 4, fourPointSign patch •
      (star (displacement - positions patch))⁻¹ ^ (power + 2))

theorem pointSourceTaylorCoefficient_relative_bound (first second : FourPointConfiguration)
    (displacement : ℂ) (power : ℕ) (circulation : ℝ) {receiverRadius radius distance : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (separated : radius + distance ≤ ‖displacement‖)
    (firstBound : ∀ patch, ‖first patch‖ ≤ radius)
    (secondBound : ∀ patch, ‖second patch‖ ≤ radius) :
    ‖pointSourceTaylorCoefficient circulation receiverRadius first displacement power -
      pointSourceTaylorCoefficient circulation receiverRadius second displacement power‖ ≤
      (|circulation| / (2 * Real.pi)) * (receiverRadius / distance) ^ power *
        (((power + 2 : ℝ) * distance⁻¹ ^ 3) * ‖fourPointSignedMoment first - fourPointSignedMoment second‖ +
          ((power + 2 : ℝ) * (power + 3 : ℝ) * distance⁻¹ ^ 4 * radius) *
            ∑ patch : Fin 4, ‖first patch - second patch‖) := by
  have actual := fourPoint_inverse_power_relative_bound first second displacement (power + 1)
    radiusNonnegative positive separated firstBound secondBound
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_one] at actual
  unfold pointSourceTaylorCoefficient
  rw [← mul_sub, ← smul_sub, norm_mul, norm_smul, Real.norm_eq_abs]
  have prefactorNorm :
      ‖(-1 : ℂ) ^ (power + 1) * Complex.I * (receiverRadius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)‖ =
        receiverRadius ^ power / (2 * Real.pi) := by
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg receiverNonnegative,
      abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_of_pos Real.pi_pos, one_mul] <;> norm_num
  rw [prefactorNorm]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left actual (abs_nonneg circulation))
    (by positivity : 0 ≤ receiverRadius ^ power / (2 * Real.pi))).trans_eq
  simp only [div_pow, pow_add]
  ring

theorem pointSourceTaylorCoefficient_relative_weighted_term_le (first second : FourPointConfiguration)
    (displacement : ℂ) (power : ℕ) (circulation : ℝ) {receiverRadius radius distance weight : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (weightNonnegative : 0 ≤ weight) (separated : radius + distance ≤ ‖displacement‖)
    (firstBound : ∀ patch, ‖first patch‖ ≤ radius)
    (secondBound : ∀ patch, ‖second patch‖ ≤ radius) :
    weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius first displacement power -
        pointSourceTaylorCoefficient circulation receiverRadius second displacement power‖ ≤
      (weight * (|circulation| / (2 * Real.pi)) *
        (4 * distance⁻¹ ^ 3 * ‖fourPointSignedMoment first - fourPointSignedMoment second‖ +
          32 * distance⁻¹ ^ 4 * radius * ∑ patch : Fin 4, ‖first patch - second patch‖)) *
        (4 * weight * receiverRadius / distance) ^ power := by
  have firstDegree : (power + 2 : ℝ) ≤ 4 * (2 : ℝ) ^ power := by
    have bound : (power + 2 : ℝ) ≤ (2 : ℝ) ^ (power + 2) := by
      exact_mod_cast (Nat.lt_two_pow_self (n := power + 2)).le
    simpa only [pow_add, show (2 : ℝ) ^ 2 = 4 by norm_num, mul_comm] using bound
  have secondDegree : (power + 3 : ℝ) ≤ 8 * (2 : ℝ) ^ power := by
    have bound : (power + 3 : ℝ) ≤ (2 : ℝ) ^ (power + 3) := by
      exact_mod_cast (Nat.lt_two_pow_self (n := power + 3)).le
    simpa only [pow_add, show (2 : ℝ) ^ 3 = 8 by norm_num, mul_comm] using bound
  have linearDegree : (power + 2 : ℝ) ≤ 4 * (4 : ℝ) ^ power :=
    firstDegree.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) power) (by norm_num))
  have quadraticDegree : (power + 2 : ℝ) * (power + 3 : ℝ) ≤ 32 * (4 : ℝ) ^ power := by
    apply (mul_le_mul firstDegree secondDegree (by positivity) (by positivity)).trans_eq
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
    ring
  have actual := mul_le_mul_of_nonneg_left
    (pointSourceTaylorCoefficient_relative_bound first second displacement power circulation receiverNonnegative
      radiusNonnegative positive separated firstBound secondBound) (pow_nonneg weightNonnegative (power + 1))
  apply actual.trans
  calc
    _ ≤ weight ^ (power + 1) * ((|circulation| / (2 * Real.pi)) * (receiverRadius / distance) ^ power *
        (((4 * (4 : ℝ) ^ power) * distance⁻¹ ^ 3) * ‖fourPointSignedMoment first - fourPointSignedMoment second‖ +
          ((32 * (4 : ℝ) ^ power) * distance⁻¹ ^ 4 * radius) *
            ∑ patch : Fin 4, ‖first patch - second patch‖)) := by
      gcongr
    _ = _ := by simp only [pow_succ, div_pow, mul_pow]; ring

end EulerNonuniqueness.Section6
