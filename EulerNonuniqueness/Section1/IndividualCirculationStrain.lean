import EulerNonuniqueness.Section1.ExternalFieldScaleBounds
import EulerNonuniqueness.Section1.DyadicSeparation

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.circulation_le_strain (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (index : ℕ) :
    scales.circulation (index + 1) ≤ scales.strain := by
  have circulationNonnegative := (scales.circulation_pos
    (zero_lt_one.trans_le frequencyBound) (by linarith) (index + 1)).le
  have locationPositive := scales.location_pos (index + 1)
  have locationBound : scales.location (index + 1) ≤ 1 := by
    have bound := scales.location_antitone (Nat.zero_le (index + 1))
    simpa only [Scales.location_eq_inv_pow, pow_zero, inv_one] using bound
  have denominatorBound : scales.location (index + 1) ^ 2 ≤ 1 := by
    nlinarith
  have individual := (scales.circulation_location_summable frequencyBound ratioBound alphaPositive 2).le_tsum
    index (fun source _ => div_nonneg
      (scales.circulation_pos (zero_lt_one.trans_le frequencyBound) (by linarith) _).le
      (sq_nonneg _))
  apply le_trans _ individual
  exact (le_div_iff₀ (sq_pos_of_pos locationPositive)).mpr
    (mul_le_of_le_one_right circulationNonnegative denominatorBound)

theorem Scales.omega_length_sq_le_strain (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (index : ℕ) :
    scales.omega (index + 1) * scales.length (index + 1) ^ 2 ≤ scales.strain / (2 * Real.pi) := by
  apply (le_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
  have bound := scales.circulation_le_strain frequencyBound ratioBound alphaPositive index
  simpa only [Scales.circulation, mul_assoc, mul_comm, mul_left_comm] using bound

end EulerNonuniqueness.Paper
