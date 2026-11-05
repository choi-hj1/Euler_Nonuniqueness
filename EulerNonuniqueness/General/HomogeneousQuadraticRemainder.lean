import Mathlib

namespace EulerNonuniqueness.General

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℂ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target]

theorem quadratic_remainder_of_unit_lines
    (function candidate : Domain → Target) (point : Domain) {radius constant : ℝ}
    (homogeneous : ∀ (scalar : ℂ) (direction : Domain),
      candidate (scalar • direction) = scalar • candidate direction)
    (bounded : ∀ direction, ‖direction‖ = 1 → ∀ parameter : ℂ, ‖parameter‖ ≤ radius →
      ‖function (point + parameter • direction) - function point - parameter • candidate direction‖ ≤
        constant * ‖parameter‖ ^ 2)
    (increment : Domain) (small : ‖increment‖ ≤ radius) :
    ‖function (point + increment) - function point - candidate increment‖ ≤
      constant * ‖increment‖ ^ 2 := by
  by_cases zero : increment = 0
  · subst increment
    have candidateZero := homogeneous (0 : ℂ) (0 : Domain)
    simp only [zero_smul] at candidateZero
    simp only [add_zero, sub_self, candidateZero, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, le_refl]
  have positive : 0 < ‖increment‖ := norm_pos_iff.mpr zero
  have scalarNonzero : (‖increment‖ : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  let direction := (‖increment‖ : ℂ)⁻¹ • increment
  have unit : ‖direction‖ = 1 := by
    dsimp only [direction]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive,
      inv_mul_cancel₀ positive.ne']
  have restoration : (‖increment‖ : ℂ) • direction = increment := by
    dsimp only [direction]
    rw [smul_smul, mul_inv_cancel₀ scalarNonzero, one_smul]
  have parameterNorm : ‖(‖increment‖ : ℂ)‖ = ‖increment‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  have estimate := bounded direction unit (‖increment‖ : ℂ) (parameterNorm.le.trans small)
  have candidateRestoration := homogeneous (‖increment‖ : ℂ) direction
  rw [restoration] at candidateRestoration
  simpa only [restoration, ← candidateRestoration, parameterNorm] using estimate

end EulerNonuniqueness.General
