import Mathlib

noncomputable section

namespace EulerNonuniqueness.Section6

theorem complex_pow_difference_bound {first second : ℂ} {bound : ℝ}
    (boundNonnegative : 0 ≤ bound) (firstBound : ‖first‖ ≤ bound) (secondBound : ‖second‖ ≤ bound)
    (power : ℕ) :
    ‖first ^ (power + 1) - second ^ (power + 1)‖ ≤
      (power + 1 : ℝ) * bound ^ power * ‖first - second‖ := by
  induction power with
  | zero => simp
  | succ power induction =>
    have identity : first ^ (power + 1 + 1) - second ^ (power + 1 + 1) =
        first * (first ^ (power + 1) - second ^ (power + 1)) + (first - second) * second ^ (power + 1) := by ring
    rw [identity]
    have firstEstimate := mul_le_mul firstBound induction (norm_nonneg _) boundNonnegative
    have secondEstimate := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) secondBound (power + 1))
      (norm_nonneg (first - second))
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul, norm_pow]
    exact (add_le_add firstEstimate secondEstimate).trans_eq (by push_cast; ring)

def coMovingInversePowerKernel (power : ℕ) (first second : ℂ) : ℂ :=
  (first / second * (star first)⁻¹ ^ power - second / first * (star second)⁻¹ ^ power) / (first - second)

theorem coMovingInversePowerKernel_swap (power : ℕ) (first second : ℂ) :
    coMovingInversePowerKernel power second first = coMovingInversePowerKernel power first second := by
  unfold coMovingInversePowerKernel
  rw [show second - first = -(first - second) by ring]
  rw [div_neg, ← neg_div]
  congr 1
  ring

theorem coMovingInversePowerKernel_far_bound {first second : ℂ} {distance : ℝ}
    (distancePositive : 0 < distance) (firstSeparated : distance ≤ ‖first‖) (secondSeparated : distance ≤ ‖second‖)
    (far : 2 * ‖second‖ ≤ ‖first‖) (power : ℕ) :
    ‖coMovingInversePowerKernel (power + 3) first second‖ ≤
      4 * distance⁻¹ ^ power * ‖first‖⁻¹ ^ 2 * ‖second‖⁻¹ ^ 2 := by
  have firstPositive := distancePositive.trans_le firstSeparated
  have secondPositive := distancePositive.trans_le secondSeparated
  have firstNonzero := norm_pos_iff.mp firstPositive
  have secondNonzero := norm_pos_iff.mp secondPositive
  have differenceLower : ‖first‖ / 2 ≤ ‖first - second‖ := by
    have triangle : ‖first‖ ≤ ‖first - second‖ + ‖second‖ := by
      simpa only [sub_add_cancel] using norm_add_le (first - second) second
    linarith
  have differencePositive : 0 < ‖first - second‖ := (half_pos firstPositive).trans_le differenceLower
  have inverseOrder : ‖first‖⁻¹ ≤ ‖second‖⁻¹ :=
    inv_anti₀ secondPositive (by linarith)
  have firstPowerBound := pow_le_pow_left₀ (inv_nonneg.mpr firstPositive.le)
    (inv_anti₀ distancePositive firstSeparated) power
  have secondPowerBound := pow_le_pow_left₀ (inv_nonneg.mpr secondPositive.le)
    (inv_anti₀ distancePositive secondSeparated) power
  have numeratorBound : ‖first / second * (star first)⁻¹ ^ (power + 3) -
        second / first * (star second)⁻¹ ^ (power + 3)‖ ≤
      2 * distance⁻¹ ^ power * ‖first‖⁻¹ * ‖second‖⁻¹ ^ 2 := by
    apply (norm_sub_le _ _).trans
    simp only [norm_mul, norm_div, norm_pow, norm_inv, norm_star]
    have firstIdentity : ‖first‖ / ‖second‖ * ‖first‖⁻¹ ^ (power + 3) =
        ‖first‖⁻¹ ^ power * ‖first‖⁻¹ ^ 2 * ‖second‖⁻¹ := by
      rw [pow_add]
      field_simp
      ring
    have secondIdentity : ‖second‖ / ‖first‖ * ‖second‖⁻¹ ^ (power + 3) =
        ‖second‖⁻¹ ^ power * ‖first‖⁻¹ * ‖second‖⁻¹ ^ 2 := by
      rw [pow_add]
      field_simp
      ring
    rw [firstIdentity, secondIdentity]
    have firstEstimate : ‖first‖⁻¹ ^ power * ‖first‖⁻¹ ^ 2 * ‖second‖⁻¹ ≤
        distance⁻¹ ^ power * ‖first‖⁻¹ * ‖second‖⁻¹ ^ 2 := by
      calc
        _ ≤ distance⁻¹ ^ power * ‖first‖⁻¹ ^ 2 * ‖second‖⁻¹ := by gcongr
        _ = distance⁻¹ ^ power * ‖first‖⁻¹ * (‖first‖⁻¹ * ‖second‖⁻¹) := by ring
        _ ≤ distance⁻¹ ^ power * ‖first‖⁻¹ * (‖second‖⁻¹ * ‖second‖⁻¹) := by gcongr
        _ = _ := by ring
    have secondEstimate : ‖second‖⁻¹ ^ power * ‖first‖⁻¹ * ‖second‖⁻¹ ^ 2 ≤
        distance⁻¹ ^ power * ‖first‖⁻¹ * ‖second‖⁻¹ ^ 2 := by gcongr
    linarith
  rw [coMovingInversePowerKernel, norm_div]
  apply (div_le_div₀ (by positivity) numeratorBound (half_pos firstPositive) differenceLower).trans
  apply le_of_eq
  field_simp
  ring

theorem coMovingInversePowerKernel_comparable_bound {first second : ℂ} {distance : ℝ}
    (distancePositive : 0 < distance) (firstSeparated : distance ≤ ‖first‖) (secondSeparated : distance ≤ ‖second‖)
    (firstComparable : ‖first‖ ≤ 2 * ‖second‖)
    (distinct : first ≠ second) (power : ℕ) :
    ‖coMovingInversePowerKernel (power + 3) first second‖ ≤
      ((power + 3 : ℝ) * 2 ^ (power + 2) + 6) *
        distance⁻¹ ^ power * ‖first‖⁻¹ ^ 2 * ‖second‖⁻¹ ^ 2 := by
  have firstPositive := distancePositive.trans_le firstSeparated
  have secondPositive := distancePositive.trans_le secondSeparated
  have firstNonzero := norm_pos_iff.mp firstPositive
  have secondNonzero := norm_pos_iff.mp secondPositive
  have differencePositive : 0 < ‖first - second‖ := norm_pos_iff.mpr (sub_ne_zero.mpr distinct)
  have inverseFirst : ‖(star first)⁻¹‖ ≤ 2 * ‖first‖⁻¹ := by
    simp only [norm_inv, norm_star]
    nlinarith [inv_pos.mpr firstPositive]
  have inverseSecond : ‖(star second)⁻¹‖ ≤ 2 * ‖first‖⁻¹ := by
    have estimate : (1 : ℝ) / ‖second‖ ≤ 2 / ‖first‖ :=
      (div_le_div_iff₀ secondPositive firstPositive).mpr (by nlinarith)
    simpa only [norm_inv, norm_star, one_div, div_eq_mul_inv, one_mul] using estimate
  have inverseDifference : ‖(star first)⁻¹ - (star second)⁻¹‖ =
      ‖first - second‖ / (‖first‖ * ‖second‖) := by
    simpa only [dist_eq_norm, ← star_sub, norm_star] using
      dist_inv_inv₀ (show star first ≠ 0 by simpa using firstNonzero) (show star second ≠ 0 by simpa using secondNonzero)
  have powerDifference := complex_pow_difference_bound (by positivity : 0 ≤ 2 * ‖first‖⁻¹)
    inverseFirst inverseSecond (power + 2)
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at powerDifference
  simp only [Nat.add_assoc, Nat.reduceAdd] at powerDifference
  rw [inverseDifference] at powerDifference
  have firstPowerBound := pow_le_pow_left₀ (inv_nonneg.mpr firstPositive.le)
    (inv_anti₀ distancePositive firstSeparated) power
  have secondPowerBound := pow_le_pow_left₀ (inv_nonneg.mpr secondPositive.le)
    (inv_anti₀ distancePositive secondSeparated) power
  have firstTermBound : ‖first / second * ((star first)⁻¹ ^ (power + 3) - (star second)⁻¹ ^ (power + 3))‖ ≤
      (power + 3 : ℝ) * 2 ^ (power + 2) *
        (distance⁻¹ ^ power * ‖first‖⁻¹ ^ 2 * ‖second‖⁻¹ ^ 2 * ‖first - second‖) := by
    rw [norm_mul, norm_div]
    have estimate := mul_le_mul_of_nonneg_left powerDifference (div_nonneg firstPositive.le secondPositive.le)
    have identity : ‖first‖ / ‖second‖ *
        ((power + 2 + 1 : ℝ) * (2 * ‖first‖⁻¹) ^ (power + 2) * (‖first - second‖ / (‖first‖ * ‖second‖))) =
        (power + 3 : ℝ) * 2 ^ (power + 2) *
          (‖first‖⁻¹ ^ power * ‖first‖⁻¹ ^ 2 * ‖second‖⁻¹ ^ 2 * ‖first - second‖) := by
      rw [mul_pow, pow_add]
      field_simp
      ring
    rw [identity] at estimate
    apply estimate.trans
    gcongr
  have ratioIdentity : first / second - second / first = (first - second) * (first + second) / (first * second) := by
    field_simp
    ring
  have ratioDifference : ‖first / second - second / first‖ ≤
      ‖first - second‖ * (‖first‖ + ‖second‖) / (‖first‖ * ‖second‖) := by
    rw [ratioIdentity, norm_div, norm_mul, norm_mul]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)) (by positivity)
  have secondTermBound : ‖(first / second - second / first) * (star second)⁻¹ ^ (power + 3)‖ ≤
      6 * (distance⁻¹ ^ power * ‖first‖⁻¹ ^ 2 * ‖second‖⁻¹ ^ 2 * ‖first - second‖) := by
    rw [norm_mul, norm_pow, norm_inv, norm_star]
    have estimate := mul_le_mul_of_nonneg_right ratioDifference (by positivity : 0 ≤ ‖second‖⁻¹ ^ (power + 3))
    have radiusBound : ‖first‖ + ‖second‖ ≤ 3 * ‖second‖ := by linarith
    have ratioBound : ‖second‖⁻¹ ≤ 2 * ‖first‖⁻¹ := by
      simpa only [norm_inv, norm_star] using inverseSecond
    have firstEstimate : ‖first - second‖ * (‖first‖ + ‖second‖) / (‖first‖ * ‖second‖) * ‖second‖⁻¹ ^ (power + 3) ≤
        3 * ‖first - second‖ * ‖first‖⁻¹ * ‖second‖⁻¹ ^ power * ‖second‖⁻¹ ^ 2 * ‖second‖⁻¹ := by
      calc
        _ ≤ ‖first - second‖ * (3 * ‖second‖) / (‖first‖ * ‖second‖) * ‖second‖⁻¹ ^ (power + 3) := by gcongr
        _ = _ := by rw [pow_add]; field_simp; ring
    apply estimate.trans (firstEstimate.trans ?_)
    calc
      _ ≤ 3 * ‖first - second‖ * ‖first‖⁻¹ * distance⁻¹ ^ power * ‖second‖⁻¹ ^ 2 * (2 * ‖first‖⁻¹) := by gcongr
      _ = _ := by ring
  have decomposition : first / second * (star first)⁻¹ ^ (power + 3) - second / first * (star second)⁻¹ ^ (power + 3) =
      first / second * ((star first)⁻¹ ^ (power + 3) - (star second)⁻¹ ^ (power + 3)) +
        (first / second - second / first) * (star second)⁻¹ ^ (power + 3) := by ring
  rw [coMovingInversePowerKernel, norm_div]
  apply (div_le_iff₀ differencePositive).mpr
  rw [decomposition]
  exact (norm_add_le _ _).trans ((add_le_add firstTermBound secondTermBound).trans_eq (by ring))

theorem coMovingInversePowerKernel_bound {first second : ℂ} {distance : ℝ}
    (distancePositive : 0 < distance) (firstSeparated : distance ≤ ‖first‖) (secondSeparated : distance ≤ ‖second‖)
    (power : ℕ) :
    ‖coMovingInversePowerKernel (power + 3) first second‖ ≤
      ((power + 3 : ℝ) * 2 ^ (power + 2) + 10) *
        distance⁻¹ ^ power * ‖first‖⁻¹ ^ 2 * ‖second‖⁻¹ ^ 2 := by
  have coefficientNonnegative : 0 ≤ (power + 3 : ℝ) * (2 : ℝ) ^ (power + 2) := by positivity
  by_cases firstFar : 2 * ‖second‖ ≤ ‖first‖
  · exact (coMovingInversePowerKernel_far_bound distancePositive firstSeparated secondSeparated firstFar power).trans
      (by gcongr; linarith)
  by_cases secondFar : 2 * ‖first‖ ≤ ‖second‖
  · rw [← coMovingInversePowerKernel_swap]
    have estimate := coMovingInversePowerKernel_far_bound distancePositive secondSeparated firstSeparated secondFar power
    apply estimate.trans
    have coefficient : (4 : ℝ) ≤ (power + 3 : ℝ) * 2 ^ (power + 2) + 10 := by linarith
    have multiplied := mul_le_mul_of_nonneg_right coefficient
      (show 0 ≤ distance⁻¹ ^ power * ‖first‖⁻¹ ^ 2 * ‖second‖⁻¹ ^ 2 by positivity)
    convert multiplied using 1 <;> ring
  by_cases equal : first = second
  · subst second
    simp only [coMovingInversePowerKernel, sub_self, div_zero, norm_zero]
    positivity
  · exact (coMovingInversePowerKernel_comparable_bound distancePositive firstSeparated secondSeparated
      (by linarith) equal power).trans (by gcongr; linarith)

end EulerNonuniqueness.Section6
