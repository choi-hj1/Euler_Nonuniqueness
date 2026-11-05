import Mathlib

namespace EulerNonuniqueness.General

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℂ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target]

theorem norm_homogeneous_sub_le_of_unit_bound
    (first second : Domain → Target) {constant : ℝ}
    (firstHomogeneous : ∀ (scalar : ℂ) (direction : Domain), first (scalar • direction) = scalar • first direction)
    (secondHomogeneous : ∀ (scalar : ℂ) (direction : Domain), second (scalar • direction) = scalar • second direction)
    (bounded : ∀ direction, ‖direction‖ ≤ 1 → ‖first direction - second direction‖ ≤ constant)
    (direction : Domain) : ‖first direction - second direction‖ ≤ constant * ‖direction‖ := by
  by_cases zero : direction = 0
  · subst direction
    have firstZero := firstHomogeneous (0 : ℂ) (0 : Domain)
    have secondZero := secondHomogeneous (0 : ℂ) (0 : Domain)
    simp only [zero_smul] at firstZero secondZero
    simp only [firstZero, secondZero, sub_self, norm_zero, mul_zero, le_refl]
  have positive : 0 < ‖direction‖ := norm_pos_iff.mpr zero
  have scalarNonzero : (‖direction‖ : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  let normalized := (‖direction‖ : ℂ)⁻¹ • direction
  have unitNorm : ‖normalized‖ = 1 := by
    dsimp only [normalized]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive,
      inv_mul_cancel₀ positive.ne']
  have restoration : (‖direction‖ : ℂ) • normalized = direction := by
    dsimp only [normalized]
    rw [smul_smul, mul_inv_cancel₀ scalarNonzero, one_smul]
  have firstScale := firstHomogeneous (‖direction‖ : ℂ) normalized
  have secondScale := secondHomogeneous (‖direction‖ : ℂ) normalized
  rw [restoration] at firstScale secondScale
  rw [firstScale, secondScale, ← smul_sub, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos positive]
  exact (mul_le_mul_of_nonneg_left (bounded normalized unitNorm.le) positive.le).trans_eq (by ring)

end EulerNonuniqueness.General
