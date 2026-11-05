import EulerNonuniqueness.Section6.FullFourPointField

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Section6

theorem fourPointField_norm_le {coefficient gap : ℝ} (positions : FourPointConfiguration)
    (positive : 0 < gap) (target : Fin 4)
    (separated : ∀ source : Fin 4, source ≠ target → gap ≤ ‖positions target - positions source‖) :
    ‖fourPointField coefficient positions target‖ ≤ 4 * |coefficient| / gap := by
  have term (source : Fin 4) :
      ‖if source = target then (0 : ℂ) else
        (fourPointSign source : ℂ) / star (positions target - positions source)‖ ≤ gap⁻¹ := by
    by_cases same : source = target
    · simp only [if_pos same, norm_zero]
      positivity
    · rw [if_neg same, norm_div, norm_star]
      have sign : ‖(fourPointSign source : ℂ)‖ = 1 := by
        unfold fourPointSign
        split_ifs <;> norm_num
      rw [sign, one_div]
      exact inv_anti₀ positive (separated source same)
  have triangle := norm_sum_le (Finset.univ : Finset (Fin 4))
    (fun source => if source = target then (0 : ℂ) else
      (fourPointSign source : ℂ) / star (positions target - positions source))
  have total := Finset.sum_le_sum (fun source (_ : source ∈ (Finset.univ : Finset (Fin 4))) => term source)
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at total
  unfold fourPointField
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |coefficient| * (4 * gap⁻¹) := mul_le_mul_of_nonneg_left (triangle.trans total) (abs_nonneg _)
    _ = _ := by ring

end EulerNonuniqueness.Section6
