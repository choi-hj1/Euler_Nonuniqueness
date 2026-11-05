import Mathlib

namespace EulerNonuniqueness.General

theorem halfIntegerImaginary_inverse_norm_le (integer : ℤ) :
    ‖(Complex.I * (integer : ℂ) / 2)⁻¹‖ ≤ 2 := by
  by_cases zero : integer = 0
  · simp [zero]
  have absolute : (1 : ℝ) ≤ |(integer : ℝ)| := by
    exact_mod_cast Int.one_le_abs zero
  have normInteger : ‖(integer : ℂ)‖ = |(integer : ℝ)| := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_inv, norm_div, norm_mul, Complex.norm_I, one_mul, normInteger]
  norm_num
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < |(integer : ℝ)|)).mpr
  linarith

end EulerNonuniqueness.General
