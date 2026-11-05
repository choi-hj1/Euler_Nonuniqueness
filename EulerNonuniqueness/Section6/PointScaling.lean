import EulerNonuniqueness.Section6.NormalizedPointOrbit

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointField_complex_dilation (coefficient : ℝ) (scale : ℂ) (positions : FourPointConfiguration) :
    fourPointField coefficient (fun target => scale * positions target) =
      fun target => (coefficient : ℂ) / star scale * fourPointField 1 positions target := by
  funext target
  have summand (source : Fin 4) :
      (if source = target then 0 else (fourPointSign source : ℂ) /
        star (scale * positions target - scale * positions source)) =
      (star scale)⁻¹ * (if source = target then 0 else (fourPointSign source : ℂ) /
        star (positions target - positions source)) := by
    by_cases same : source = target
    · simp only [same, if_true, mul_zero]
    · simp only [same, if_false, ← mul_sub, star_mul, div_eq_mul_inv, mul_inv_rev]
      ring
  simp only [fourPointField, Complex.ofReal_one, mul_one]
  simp_rw [summand]
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv]
  ring

theorem pointShapeRatio_complex_dilation {scale : ℂ} (nonzero : scale ≠ 0) (positive negative : ℂ) :
    pointShapeRatio (scale * positive) (scale * negative) = pointShapeRatio positive negative := by
  simp only [pointShapeRatio, norm_mul, mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr nonzero))]

theorem pointShapeForcing_complex_dilation {scale : ℂ} (nonzero : scale ≠ 0)
    (positive negative positiveForcing negativeForcing : ℂ) :
    pointShapeForcing (scale * positive) (scale * negative) (scale * positiveForcing) (scale * negativeForcing) =
      pointShapeForcing positive negative positiveForcing negativeForcing := by
  simp only [pointShapeForcing, pointShapeRatio_complex_dilation nonzero,
    mul_div_mul_left _ _ nonzero]

theorem fourPointField_physical_dilation (frequency length : ℝ) {direction : ℂ}
    (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1) (positions : FourPointConfiguration) :
    fourPointField (frequency * length ^ 2) (fun target => (length : ℂ) * direction * positions target) =
      fun target => ((frequency * length : ℝ) : ℂ) * direction * fourPointField 1 positions target := by
  have directionNonzero : direction ≠ 0 := norm_ne_zero_iff.mp (by rw [directionNorm]; norm_num)
  have unitProduct : star direction * direction = 1 := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, directionNorm, one_pow, Complex.ofReal_one] using
      (Complex.normSq_eq_conj_mul_self (z := direction)).symm
  have inverse : (star direction)⁻¹ = direction :=
    (mul_eq_one_iff_inv_eq₀ (star_ne_zero.mpr directionNonzero)).mp unitProduct
  have starLength : star (length : ℂ) = (length : ℂ) := by simp [Complex.star_def]
  rw [fourPointField_complex_dilation]
  funext target
  simp only [star_mul, starLength, div_eq_mul_inv, mul_inv_rev, inverse]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr lengthPositive.ne']
  ring

end EulerNonuniqueness.Section6
