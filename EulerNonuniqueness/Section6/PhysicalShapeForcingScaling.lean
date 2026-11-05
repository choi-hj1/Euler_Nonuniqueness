import EulerNonuniqueness.Section6.InternalShapeScaling

namespace EulerNonuniqueness.Section6

theorem pointShapeForcing_real_mul (scalar : ℝ)
    (positive negative positiveForcing negativeForcing : ℂ) :
    pointShapeForcing positive negative ((scalar : ℂ) * positiveForcing) ((scalar : ℂ) * negativeForcing) =
      scalar • pointShapeForcing positive negative positiveForcing negativeForcing := by
  have differenceIdentity : (scalar : ℂ) * negativeForcing / negative -
      (scalar : ℂ) * positiveForcing / positive =
      (scalar : ℂ) * (negativeForcing / negative - positiveForcing / positive) := by ring
  unfold pointShapeForcing
  dsimp only
  rw [differenceIdentity]
  ext <;> simp [Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

theorem complex_scale_coefficient_identity (coefficient : ℝ) {scale : ℂ} (scaleNonzero : scale ≠ 0) :
    scale * ((coefficient / ‖scale‖ ^ 2 : ℝ) : ℂ) = (coefficient : ℂ) / star scale := by
  have product : scale * star scale = ((‖scale‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using Complex.mul_conj scale
  have normNonzero : ((‖scale‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr scaleNonzero)
  apply (eq_div_iff (star_ne_zero.mpr scaleNonzero)).mpr
  calc
    _ = (scale * star scale) * ((coefficient / ‖scale‖ ^ 2 : ℝ) : ℂ) := by ring
    _ = _ := by
      rw [product, Complex.ofReal_div]
      field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr scaleNonzero)]

theorem pointShapeForcing_physical_dilation (coefficient : ℝ) {scale : ℂ}
    (scaleNonzero : scale ≠ 0) (positive negative positiveForcing negativeForcing : ℂ) :
    pointShapeForcing (scale * positive) (scale * negative)
      (((coefficient : ℂ) / star scale) * positiveForcing)
      (((coefficient : ℂ) / star scale) * negativeForcing) =
        (coefficient / ‖scale‖ ^ 2 : ℝ) •
          pointShapeForcing positive negative positiveForcing negativeForcing := by
  calc
    _ = pointShapeForcing (scale * positive) (scale * negative)
        (scale * (((coefficient / ‖scale‖ ^ 2 : ℝ) : ℂ) * positiveForcing))
        (scale * (((coefficient / ‖scale‖ ^ 2 : ℝ) : ℂ) * negativeForcing)) := by
      rw [← complex_scale_coefficient_identity coefficient scaleNonzero]
      congr 1 <;> ring
    _ = pointShapeForcing positive negative
        (((coefficient / ‖scale‖ ^ 2 : ℝ) : ℂ) * positiveForcing)
        (((coefficient / ‖scale‖ ^ 2 : ℝ) : ℂ) * negativeForcing) :=
      pointShapeForcing_complex_dilation scaleNonzero _ _ _ _
    _ = _ := pointShapeForcing_real_mul _ _ _ _ _

end EulerNonuniqueness.Section6
