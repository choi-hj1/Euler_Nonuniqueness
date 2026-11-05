import EulerNonuniqueness.Section6.CauchyStrainKernelMultipole
import EulerNonuniqueness.Section6.MovingPatchStrain

noncomputable section

namespace EulerNonuniqueness.Section6

theorem cauchyStrain_linear_remainder_bound {position : ℂ} (small : ‖position‖ ≤ 1 / 2) :
    ‖1 / (1 - position) ^ 2 - 1 - 2 * position‖ ≤ 16 * ‖position‖ ^ 2 := by
  have inverseBound := norm_inv_one_sub_le_two small
  have nonzero : 1 - position ≠ 0 := by
    intro zero
    have equality : position = 1 := (sub_eq_zero.mp zero).symm
    rw [equality, norm_one] at small
    norm_num at small
  have identity : 1 / (1 - position) ^ 2 - 1 - 2 * position =
      position ^ 2 * (3 - 2 * position) * ((1 - position)⁻¹) ^ 2 := by
    field_simp [nonzero]
    ring
  have numerator : ‖3 - 2 * position‖ ≤ 4 := by
    have estimate := norm_sub_le (3 : ℂ) (2 * position)
    norm_num only [norm_mul, Complex.norm_ofNat] at estimate
    linarith
  have inverseSquare : ‖((1 - position)⁻¹) ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    nlinarith [pow_le_pow_left₀ (norm_nonneg ((1 - position)⁻¹)) inverseBound 2]
  rw [identity, norm_mul, norm_mul, norm_pow]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left numerator (sq_nonneg _)) inverseSquare
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem cauchyStrain_source_linear_taylor_bound {location center source : ℂ} {radius : ℝ}
    (locationPositive : 0 < ‖location - center‖) (sourceBound : ‖source - center‖ ≤ radius)
    (separated : 2 * radius ≤ ‖location - center‖) :
    ‖1 / (location - source) ^ 2 - 1 / (location - center) ^ 2 -
        2 * (source - center) / (location - center) ^ 3‖ ≤
      16 * radius ^ 2 / ‖location - center‖ ^ 4 := by
  have radiusNonnegative := (norm_nonneg _).trans sourceBound
  have locationNonzero := norm_pos_iff.mp locationPositive
  have quotientBound : ‖(source - center) / (location - center)‖ ≤ radius / ‖location - center‖ := by
    rw [norm_div]
    exact div_le_div_of_nonneg_right sourceBound locationPositive.le
  have quotientSmall : ‖(source - center) / (location - center)‖ ≤ 1 / 2 :=
    quotientBound.trans ((div_le_iff₀ locationPositive).mpr (by linarith))
  have identity :
      1 / (location - source) ^ 2 - 1 / (location - center) ^ 2 -
        2 * (source - center) / (location - center) ^ 3 =
      (1 / (1 - (source - center) / (location - center)) ^ 2 - 1 -
        2 * ((source - center) / (location - center))) / (location - center) ^ 2 := by
    have normalized : 1 - (source - center) / (location - center) =
        (location - source) / (location - center) := by field_simp <;> ring
    rw [normalized]
    field_simp [locationNonzero]
    <;> ring
  rw [identity, norm_div, norm_pow]
  have estimate := (cauchyStrain_linear_remainder_bound quotientSmall).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) quotientBound 2) (by norm_num))
  exact (div_le_div_of_nonneg_right estimate (sq_nonneg _)).trans_eq (by ring)

def kernelStrainSourceTaylorRemainder (position center source : ℂ) : ℂ :=
  biotSavartKernelStrain position source - biotSavartKernelStrain position center +
    2 * (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star ((source - center) / (position - center) ^ 3)

theorem kernelStrainSourceTaylorRemainder_bound {position center source : ℂ} {radius : ℝ}
    (locationPositive : 0 < ‖position - center‖) (sourceBound : ‖source - center‖ ≤ radius)
    (separated : 2 * radius ≤ ‖position - center‖) :
    ‖kernelStrainSourceTaylorRemainder position center source‖ ≤
      8 * radius ^ 2 / (Real.pi * ‖position - center‖ ^ 4) := by
  have identity : kernelStrainSourceTaylorRemainder position center source =
      -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (
        1 / (position - source) ^ 2 - 1 / (position - center) ^ 2 -
        2 * (source - center) / (position - center) ^ 3) := by
    simp only [kernelStrainSourceTaylorRemainder, biotSavartKernelStrain, star_sub, star_div₀, star_pow,
      star_mul, star_one, Complex.star_def, Complex.conj_ofNat]
    ring
  rw [identity, norm_mul, norm_neg, norm_star]
  have coefficient : ‖Complex.I / ((2 * Real.pi : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [coefficient]
  exact (mul_le_mul_of_nonneg_left (cauchyStrain_source_linear_taylor_bound locationPositive sourceBound separated)
    (by positivity : 0 ≤ 1 / (2 * Real.pi))).trans_eq (by ring)

end EulerNonuniqueness.Section6
