import EulerNonuniqueness.Section6.TemporalCoefficientEnvelope
import Mathlib.Data.Nat.Choose.Cast

noncomputable section

namespace EulerNonuniqueness.Section6

theorem shifted_linear_half_hasSum :
    HasSum (fun power : ℕ => (power + 2 : ℝ) * (1 / 2 : ℝ) ^ power) 6 := by
  have linear := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
  have constant := (hasSum_geometric_of_norm_lt_one (ξ := (1 / 2 : ℝ)) (by norm_num)).mul_left 2
  convert linear.add constant using 1
  · funext power
    ring
  · norm_num

theorem shifted_quadratic_half_hasSum :
    HasSum (fun power : ℕ => (power + 2 : ℝ) * (power + 3 : ℝ) * (1 / 2 : ℝ) ^ power) 28 := by
  have quadratic := (hasSum_choose_mul_geometric_of_norm_lt_one 2 (r := (1 / 2 : ℝ)) (by norm_num)).mul_left 2
  have linear := (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left 2
  have constant := (hasSum_geometric_of_norm_lt_one (ξ := (1 / 2 : ℝ)) (by norm_num)).mul_left 4
  convert (quadratic.add linear).add constant using 1
  · funext power
    rw [Nat.cast_choose_two]
    push_cast
    ring
  · norm_num

theorem temporalCoefficientEnvelope_split (radius distance weight mass : ℝ) (power : ℕ) :
    (2 : ℝ) ^ (power + 1) * temporalCoefficientEnvelope radius distance weight mass power =
      ((power + 2 : ℝ) * (power + 3 : ℝ) * (4 * radius / distance) ^ power) * (weight ^ 2 / Real.pi ^ 2) +
      ((power + 2 : ℝ) * (2 * radius / distance) ^ power) *
        (2 * radius / distance * weight ^ 2 / Real.pi ^ 2 + 5 * weight ^ 2 / (2 * Real.pi ^ 2) +
          mass * weight / (Real.pi ^ 2 * distance ^ 2)) := by
  unfold temporalCoefficientEnvelope
  simp only [Nat.cast_add, Nat.cast_ofNat, pow_add, pow_succ, div_pow, mul_pow, inv_pow,
    show (4 : ℝ) = 2 * 2 by norm_num]
  ring

theorem tsum_weighted_temporalCoefficientEnvelope_le {radius distance weight mass : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass)
    (small : 8 * radius ≤ distance) :
    (∑' power : ℕ, (2 : ℝ) ^ (power + 1) * temporalCoefficientEnvelope radius distance weight mass power) ≤
      28 * (weight ^ 2 / Real.pi ^ 2) + 6 *
        (2 * radius / distance * weight ^ 2 / Real.pi ^ 2 + 5 * weight ^ 2 / (2 * Real.pi ^ 2) +
          mass * weight / (Real.pi ^ 2 * distance ^ 2)) := by
  have firstRatio : 4 * radius / distance ≤ 1 / 2 := (div_le_iff₀ positive).mpr (by linarith)
  have secondRatio : 2 * radius / distance ≤ 1 / 2 := (div_le_iff₀ positive).mpr (by linarith)
  have strictSmall : 4 * radius / distance < 1 := firstRatio.trans_lt (by norm_num)
  have coefficientNonnegative : 0 ≤ 2 * radius / distance * weight ^ 2 / Real.pi ^ 2 +
      5 * weight ^ 2 / (2 * Real.pi ^ 2) + mass * weight / (Real.pi ^ 2 * distance ^ 2) := by positivity
  have first := shifted_quadratic_half_hasSum.mul_right (weight ^ 2 / Real.pi ^ 2)
  have second := shifted_linear_half_hasSum.mul_right
    (2 * radius / distance * weight ^ 2 / Real.pi ^ 2 + 5 * weight ^ 2 / (2 * Real.pi ^ 2) +
      mass * weight / (Real.pi ^ 2 * distance ^ 2))
  rw [← (first.add second).tsum_eq]
  apply Summable.tsum_le_tsum
    (fun power => ?_)
    (summable_weighted_temporalCoefficientEnvelope radiusNonnegative positive strictSmall weight mass)
    (first.add second).summable
  rw [temporalCoefficientEnvelope_split]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : 0 ≤ 4 * radius / distance) firstRatio power) (by positivity)
  · apply mul_le_mul_of_nonneg_right _ coefficientNonnegative
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : 0 ≤ 2 * radius / distance) secondRatio power) (by positivity)

theorem tsum_weighted_temporalCoefficientEnvelope_coarse {radius distance weight mass : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass)
    (small : 8 * radius ≤ distance) :
    (∑' power : ℕ, (2 : ℝ) ^ (power + 1) * temporalCoefficientEnvelope radius distance weight mass power) ≤
      46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2) := by
  have ratio : 2 * radius / distance ≤ 1 / 2 := (div_le_iff₀ positive).mpr (by linarith)
  have termBound := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ratio (sq_nonneg weight)) (sq_nonneg Real.pi)
  have secondBound : 2 * radius / distance * weight ^ 2 / Real.pi ^ 2 +
      5 * weight ^ 2 / (2 * Real.pi ^ 2) + mass * weight / (Real.pi ^ 2 * distance ^ 2) ≤
      3 * (weight ^ 2 / Real.pi ^ 2) + mass * weight / (Real.pi ^ 2 * distance ^ 2) := by
    have estimate := add_le_add_right (add_le_add_right termBound (5 * weight ^ 2 / (2 * Real.pi ^ 2)))
      (mass * weight / (Real.pi ^ 2 * distance ^ 2))
    convert estimate using 1 <;> ring
  have estimate := add_le_add_left (mul_le_mul_of_nonneg_left secondBound (by norm_num : (0 : ℝ) ≤ 6))
    (28 * (weight ^ 2 / Real.pi ^ 2))
  have finalBound : 28 * (weight ^ 2 / Real.pi ^ 2) + 6 *
      (2 * radius / distance * weight ^ 2 / Real.pi ^ 2 + 5 * weight ^ 2 / (2 * Real.pi ^ 2) +
        mass * weight / (Real.pi ^ 2 * distance ^ 2)) ≤
      46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2) := by
    convert estimate using 1 <;> ring
  exact (tsum_weighted_temporalCoefficientEnvelope_le radiusNonnegative positive weightNonnegative massNonnegative small).trans finalBound

theorem tsum_weighted_spatialCoefficientEnvelope_le {radius distance weight : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (small : 4 * radius ≤ distance) :
    (∑' power : ℕ, (2 : ℝ) ^ (power + 1) * ((radius / distance) ^ power * (weight / (2 * Real.pi)))) ≤
      2 * weight / Real.pi := by
  have ratio : 2 * radius / distance ≤ 1 / 2 := (div_le_iff₀ positive).mpr (by linarith)
  have nonnegative : 0 ≤ 2 * radius / distance := by positivity
  have strictSmall : 2 * radius / distance < 1 := ratio.trans_lt (by norm_num)
  have identity (power : ℕ) : (2 : ℝ) ^ (power + 1) * ((radius / distance) ^ power * (weight / (2 * Real.pi))) =
      (2 * radius / distance) ^ power * (weight / Real.pi) := by
    rw [show 2 * radius / distance = 2 * (radius / distance) by ring, mul_pow, pow_succ]
    ring
  simp_rw [identity]
  rw [tsum_mul_right, tsum_geometric_of_lt_one nonnegative strictSmall]
  have inverseBound := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2)
    (show 1 / 2 ≤ 1 - 2 * radius / distance by linarith)
  norm_num only [one_div, inv_inv] at inverseBound
  have estimate := mul_le_mul_of_nonneg_right inverseBound (div_nonneg weightNonnegative Real.pi_pos.le)
  convert estimate using 1 <;> ring

end EulerNonuniqueness.Section6
