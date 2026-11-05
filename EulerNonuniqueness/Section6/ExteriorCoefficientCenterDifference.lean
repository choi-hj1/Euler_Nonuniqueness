import EulerNonuniqueness.Section6.ExteriorCoefficientBound
import EulerNonuniqueness.Section6.CoMovingInversePowerKernel

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Section6

theorem conjugate_inverse_power_difference_bound {first second : ℂ} {distance : ℝ}
    (positive : 0 < distance) (firstSeparated : distance ≤ ‖first‖)
    (secondSeparated : distance ≤ ‖second‖) (power : ℕ) :
    ‖(star first)⁻¹ ^ (power + 1) - (star second)⁻¹ ^ (power + 1)‖ ≤
      (power + 1 : ℝ) * distance⁻¹ ^ (power + 2) * ‖first - second‖ := by
  have firstNonzero := norm_pos_iff.mp (positive.trans_le firstSeparated)
  have secondNonzero := norm_pos_iff.mp (positive.trans_le secondSeparated)
  have inverseDifference : ‖(star first)⁻¹ - (star second)⁻¹‖ ≤
      distance⁻¹ ^ 2 * ‖first - second‖ := by
    have identity := dist_inv_inv₀ (show star first ≠ 0 by simpa using firstNonzero)
      (show star second ≠ 0 by simpa using secondNonzero)
    simp only [dist_eq_norm, ← star_sub, norm_star] at identity
    rw [identity]
    have denominator : distance ^ 2 ≤ ‖first‖ * ‖second‖ := by
      nlinarith [mul_le_mul firstSeparated secondSeparated positive.le (norm_nonneg first)]
    apply (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) denominator).trans_eq
    ring
  have inverseFirst : ‖(star first)⁻¹‖ ≤ distance⁻¹ := by
    simpa only [norm_inv, norm_star] using inv_anti₀ positive firstSeparated
  have inverseSecond : ‖(star second)⁻¹‖ ≤ distance⁻¹ := by
    simpa only [norm_inv, norm_star] using inv_anti₀ positive secondSeparated
  have bound := complex_pow_difference_bound (inv_nonneg.mpr positive.le) inverseFirst inverseSecond power
  apply bound.trans
  calc
    _ ≤ (power + 1 : ℝ) * distance⁻¹ ^ power * (distance⁻¹ ^ 2 * ‖first - second‖) := by gcongr
    _ = _ := by rw [pow_add]; ring

theorem norm_integral_exterior_inverse_power_center_difference {vorticity : Vorticity}
    (integrable : Integrable vorticity) (first second : ℂ) {distance : ℝ} (positive : 0 < distance)
    (firstSeparated : ∀ position ∈ Function.support vorticity, distance ≤ ‖first - position‖)
    (secondSeparated : ∀ position ∈ Function.support vorticity, distance ≤ ‖second - position‖)
    (power : ℕ) :
    ‖(∫ position, vorticity position • (star (first - position))⁻¹ ^ (power + 2)) -
      (∫ position, vorticity position • (star (second - position))⁻¹ ^ (power + 2))‖ ≤
      ((power + 2 : ℝ) * distance⁻¹ ^ (power + 3) * ‖first - second‖) *
        ∫ position, |vorticity position| := by
  rw [← integral_sub
    (integrable_exterior_inverse_power integrable first positive firstSeparated power)
    (integrable_exterior_inverse_power integrable second positive secondSeparated power)]
  have pointwise (position : ℂ) :
      ‖vorticity position • (star (first - position))⁻¹ ^ (power + 2) -
        vorticity position • (star (second - position))⁻¹ ^ (power + 2)‖ ≤
      ((power + 2 : ℝ) * distance⁻¹ ^ (power + 3) * ‖first - second‖) * |vorticity position| := by
    by_cases zero : vorticity position = 0
    · simp [zero]
    have actual := conjugate_inverse_power_difference_bound positive
      (firstSeparated position zero) (secondSeparated position zero) (power + 1)
    have difference : (first - position) - (second - position) = first - second := by abel
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_one, difference] at actual
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left actual (abs_nonneg _)).trans_eq (by ring)
  have estimate := norm_integral_le_of_norm_le
    (integrable.norm.const_mul ((power + 2 : ℝ) * distance⁻¹ ^ (power + 3) * ‖first - second‖))
    (Filter.Eventually.of_forall pointwise)
  simpa only [integral_const_mul, Real.norm_eq_abs] using estimate

theorem exteriorVorticityCoefficient_center_difference_norm_le {vorticity : Vorticity}
    (integrable : Integrable vorticity) (first second : ℂ) {radius distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (firstSeparated : ∀ position ∈ Function.support vorticity, distance ≤ ‖first - position‖)
    (secondSeparated : ∀ position ∈ Function.support vorticity, distance ≤ ‖second - position‖)
    (power : ℕ) :
    ‖exteriorVorticityCoefficient vorticity first radius power -
      exteriorVorticityCoefficient vorticity second radius power‖ ≤
      (power + 2 : ℝ) * (radius / distance) ^ power *
        ((distance⁻¹ ^ 3 * ‖first - second‖ * ∫ position, |vorticity position|) / (2 * Real.pi)) := by
  unfold exteriorVorticityCoefficient
  rw [← mul_sub, norm_mul]
  have actual := mul_le_mul_of_nonneg_left
    (norm_integral_exterior_inverse_power_center_difference integrable first second positive
      firstSeparated secondSeparated power)
    (norm_nonneg (((-1 : ℂ) ^ (power + 1) * Complex.I * (radius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ))))
  apply actual.trans_eq
  simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg radiusNonnegative,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), one_mul]
  rw [div_pow, pow_add]
  simp only [abs_of_pos Real.pi_pos]
  norm_num
  <;> ring

end EulerNonuniqueness.Section6
