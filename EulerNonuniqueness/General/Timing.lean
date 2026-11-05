import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Real

theorem abs_le_three_quarters_of_quadratic_recurrence
    {current next rate coefficient tolerance bound : ℝ}
    (hrate_nonneg : 0 ≤ rate) (hrate : rate ≤ 1 / 4)
    (hcoefficient : 0 ≤ coefficient) (hbound : 0 ≤ bound)
    (hquadratic : coefficient * bound ≤ 1 / 4)
    (hforcing : coefficient * tolerance ≤ bound / 4)
    (hnext : |next| ≤ bound)
    (hrecurrence : |current| ≤ rate * |next| + coefficient * |next| ^ 2 +
      coefficient * tolerance) :
    |current| ≤ 3 / 4 * bound := by
  have hlinear : rate * |next| ≤ bound / 4 := by
    calc
      rate * |next| ≤ rate * bound := mul_le_mul_of_nonneg_left hnext hrate_nonneg
      _ ≤ 1 / 4 * bound := mul_le_mul_of_nonneg_right hrate hbound
      _ = bound / 4 := by ring
  have hquadratic_bound : coefficient * |next| ^ 2 ≤ bound / 4 := by
    calc
      coefficient * |next| ^ 2 = (coefficient * |next|) * |next| := by ring
      _ ≤ (coefficient * bound) * |next| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnext hcoefficient) (abs_nonneg _)
      _ ≤ (1 / 4) * |next| :=
        mul_le_mul_of_nonneg_right hquadratic (abs_nonneg _)
      _ ≤ (1 / 4) * bound := mul_le_mul_of_nonneg_left hnext (by norm_num)
      _ = bound / 4 := by ring
  linarith

theorem descending_abs_bound_of_quadratic_recurrence
    {sequence : ℕ → ℝ} {terminal : ℕ} {rate coefficient tolerance bound : ℝ}
    (hrate_nonneg : 0 ≤ rate) (hrate : rate ≤ 1 / 4)
    (hcoefficient : 0 ≤ coefficient) (hbound : 0 ≤ bound)
    (hquadratic : coefficient * bound ≤ 1 / 4)
    (hforcing : coefficient * tolerance ≤ bound / 4)
    (hterminal : |sequence terminal| ≤ bound)
    (hrecurrence : ∀ index < terminal,
      |sequence index| ≤ rate * |sequence (index + 1)| +
        coefficient * |sequence (index + 1)| ^ 2 + coefficient * tolerance) :
    ∀ index ≤ terminal, |sequence index| ≤ bound := by
  intro index hindex
  induction hindex using Nat.decreasingInduction with
  | self => exact hterminal
  | of_succ index hindex hnext =>
    have himproved := abs_le_three_quarters_of_quadratic_recurrence
      hrate_nonneg hrate hcoefficient hbound hquadratic hforcing hnext (hrecurrence index hindex)
    linarith

end Real
