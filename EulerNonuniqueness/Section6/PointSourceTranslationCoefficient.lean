import EulerNonuniqueness.Section6.PointSourceRelativeCoefficient
import EulerNonuniqueness.Section6.SignedInversePowerTranslation
import EulerNonuniqueness.General.PolynomialGeometricMajorant

noncomputable section

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 1000000

theorem pointSourceTaylorCoefficient_translation_bound (positions : FourPointConfiguration)
    (anchor first second : ℂ) (power : ℕ) (circulation : ℝ) {receiverRadius radius travel distance : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (radiusNonnegative : 0 ≤ radius)
    (travelNonnegative : 0 ≤ travel) (positive : 0 < distance)
    (separated : radius + travel + distance ≤ ‖anchor‖)
    (positionBound : ∀ patch, ‖positions patch‖ ≤ radius)
    (firstBound : ‖first - anchor‖ ≤ travel) (secondBound : ‖second - anchor‖ ≤ travel) :
    ‖pointSourceTaylorCoefficient circulation receiverRadius positions first power -
      pointSourceTaylorCoefficient circulation receiverRadius positions second power‖ ≤
      (|circulation| / (2 * Real.pi)) * (receiverRadius / distance) ^ power *
        (((power + 2 : ℝ) * (power + 3 : ℝ) * distance⁻¹ ^ 4) * ‖fourPointSignedMoment positions‖ +
          ((power + 2 : ℝ) * (power + 3 : ℝ) * (power + 4 : ℝ) * distance⁻¹ ^ 5 * radius) *
            ∑ patch : Fin 4, ‖positions patch‖) * ‖first - second‖ := by
  have zeroMass : ∑ patch : Fin 4, fourPointSign patch = 0 := by
    norm_num [fourPointSign, Fin.sum_univ_succ]
  have momentIdentity : (∑ patch : Fin 4, fourPointSign patch • positions patch) =
      fourPointSignedMoment positions := by
    simp only [Complex.real_smul, fourPointSignedMoment]
  have absoluteSign (patch : Fin 4) : |fourPointSign patch| = 1 := by
    unfold fourPointSign
    split_ifs <;> norm_num
  have actual := signed_inverse_power_translation_bound Finset.univ fourPointSign positions zeroMass
    anchor first second (power + 1) radiusNonnegative travelNonnegative positive separated
    (fun patch _ => positionBound patch) firstBound secondBound
  simp only [momentIdentity, absoluteSign, one_mul, Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.reduceAdd] at actual
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

theorem pointSourceTaylorCoefficient_translation_weighted_term_le (positions : FourPointConfiguration)
    (anchor first second : ℂ) (power : ℕ) (circulation : ℝ) {receiverRadius radius travel distance weight : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (radiusNonnegative : 0 ≤ radius)
    (travelNonnegative : 0 ≤ travel) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (separated : radius + travel + distance ≤ ‖anchor‖)
    (positionBound : ∀ patch, ‖positions patch‖ ≤ radius)
    (firstBound : ‖first - anchor‖ ≤ travel) (secondBound : ‖second - anchor‖ ≤ travel) :
    weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius positions first power -
        pointSourceTaylorCoefficient circulation receiverRadius positions second power‖ ≤
      (weight * (|circulation| / (2 * Real.pi)) *
        (32 * distance⁻¹ ^ 4 * ‖fourPointSignedMoment positions‖ +
          512 * distance⁻¹ ^ 5 * radius * ∑ patch : Fin 4, ‖positions patch‖) * ‖first - second‖) *
        (8 * weight * receiverRadius / distance) ^ power := by
  have quadraticDegree : (power + 2 : ℝ) * (power + 3 : ℝ) ≤ 32 * (8 : ℝ) ^ power :=
    (EulerNonuniqueness.General.quadratic_natCast_degree_le_geometric power).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) power) (by norm_num))
  have cubicDegree := EulerNonuniqueness.General.cubic_natCast_degree_le_geometric power
  have actual := mul_le_mul_of_nonneg_left
    (pointSourceTaylorCoefficient_translation_bound positions anchor first second power circulation receiverNonnegative
      radiusNonnegative travelNonnegative positive separated positionBound firstBound secondBound)
    (pow_nonneg weightNonnegative (power + 1))
  apply actual.trans
  calc
    _ ≤ weight ^ (power + 1) * ((|circulation| / (2 * Real.pi)) * (receiverRadius / distance) ^ power *
        (((32 * (8 : ℝ) ^ power) * distance⁻¹ ^ 4) * ‖fourPointSignedMoment positions‖ +
          ((512 * (8 : ℝ) ^ power) * distance⁻¹ ^ 5 * radius) *
            ∑ patch : Fin 4, ‖positions patch‖) * ‖first - second‖) := by
      gcongr
    _ = _ := by simp only [pow_succ, mul_pow, div_pow]; ring

end EulerNonuniqueness.Section6
