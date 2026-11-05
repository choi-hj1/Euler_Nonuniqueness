import EulerNonuniqueness.Section3.HolderBanachModel

open Set

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem holder_product_bound (first second : PeriodicHolderHalf) (left right : ℝ) :
    ‖first.val.1 left * second.val.1 left - first.val.1 right * second.val.1 right‖ ≤
      (2 * ‖first‖ * ‖second‖) * Real.sqrt |left - right| := by
  have identity : first.val.1 left * second.val.1 left - first.val.1 right * second.val.1 right =
      (first.val.1 left - first.val.1 right) * second.val.1 left +
        first.val.1 right * (second.val.1 left - second.val.1 right) := by ring
  rw [identity]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (‖first‖ * Real.sqrt |left - right|) * ‖second‖ +
        ‖first‖ * (‖second‖ * Real.sqrt |left - right|) :=
      add_le_add
        (mul_le_mul (PeriodicHolderHalf.holder_bound first left right) (PeriodicHolderHalf.value_bound second left)
          (norm_nonneg _) (by positivity))
        (mul_le_mul (PeriodicHolderHalf.value_bound first right) (PeriodicHolderHalf.holder_bound second left right)
          (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

def holderProduct (first second : PeriodicHolderHalf) : PeriodicHolderHalf :=
  PeriodicHolderHalf.ofFunction (fun label => first.val.1 label * second.val.1 label)
    (first.val.1.continuous.mul second.val.1.continuous)
    (‖first‖ * ‖second‖) (2 * ‖first‖ * ‖second‖)
    (fun label => by
      rw [norm_mul]
      exact mul_le_mul (PeriodicHolderHalf.value_bound first label) (PeriodicHolderHalf.value_bound second label)
        (norm_nonneg _) (norm_nonneg _))
    (holder_product_bound first second)
    (fun label => by dsimp only; rw [PeriodicHolderHalf.periodic first label, PeriodicHolderHalf.periodic second label])

theorem holderProduct_value (first second : PeriodicHolderHalf) (label : ℝ) :
    (holderProduct first second).val.1 label = first.val.1 label * second.val.1 label := rfl

def holderConjugate (density : PeriodicHolderHalf) : PeriodicHolderHalf :=
  PeriodicHolderHalf.ofFunction (fun label => star (density.val.1 label)) density.val.1.continuous.star
    ‖density‖ ‖density‖
    (fun label => by rw [norm_star]; exact PeriodicHolderHalf.value_bound density label)
    (fun first second => by rw [← star_sub, norm_star]; exact PeriodicHolderHalf.holder_bound density first second)
    (fun label => by dsimp only; rw [PeriodicHolderHalf.periodic density label])

theorem holderConjugate_value (density : PeriodicHolderHalf) (label : ℝ) :
    (holderConjugate density).val.1 label = star (density.val.1 label) := rfl

def holderComplexMul (scalar : ℂ) (density : PeriodicHolderHalf) : PeriodicHolderHalf :=
  PeriodicHolderHalf.ofFunction (fun label => scalar * density.val.1 label)
    (continuous_const.mul density.val.1.continuous) (‖scalar‖ * ‖density‖) (‖scalar‖ * ‖density‖)
    (fun label => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (PeriodicHolderHalf.value_bound density label) (norm_nonneg _))
    (fun first second => by
      rw [← mul_sub, norm_mul]
      exact (mul_le_mul_of_nonneg_left (PeriodicHolderHalf.holder_bound density first second)
        (norm_nonneg _)).trans_eq (by ring))
    (fun label => by dsimp only; rw [PeriodicHolderHalf.periodic density label])

theorem holderComplexMul_value (scalar : ℂ) (density : PeriodicHolderHalf) (label : ℝ) :
    (holderComplexMul scalar density).val.1 label = scalar * density.val.1 label := rfl

theorem holder_inverse_bound (density : PeriodicHolderHalf) {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ label : ℝ, lower ≤ ‖density.val.1 label‖) (first second : ℝ) :
    ‖(density.val.1 first)⁻¹ - (density.val.1 second)⁻¹‖ ≤
      (‖density‖ / lower ^ 2) * Real.sqrt |first - second| := by
  have first_pos := lower_pos.trans_le (separated first)
  have second_pos := lower_pos.trans_le (separated second)
  have identity := dist_inv_inv₀ (norm_ne_zero_iff.mp first_pos.ne') (norm_ne_zero_iff.mp second_pos.ne')
  simp only [dist_eq_norm] at identity
  rw [identity]
  calc
    _ ≤ ‖density.val.1 first - density.val.1 second‖ / (lower * lower) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos lower_pos lower_pos)
        (mul_le_mul (separated first) (separated second) lower_pos.le (norm_nonneg _))
    _ ≤ (‖density‖ * Real.sqrt |first - second|) / (lower * lower) :=
      div_le_div_of_nonneg_right (PeriodicHolderHalf.holder_bound density first second) (by positivity)
    _ = _ := by ring

def holderInverse (density : PeriodicHolderHalf) {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ label : ℝ, lower ≤ ‖density.val.1 label‖) : PeriodicHolderHalf :=
  PeriodicHolderHalf.ofFunction (fun label => (density.val.1 label)⁻¹)
    (density.val.1.continuous.inv₀ (fun label =>
      norm_ne_zero_iff.mp (ne_of_gt (lower_pos.trans_le (separated label)))))
    (1 / lower) (‖density‖ / lower ^ 2)
    (fun label => by
      rw [norm_inv, one_div]
      exact inv_anti₀ lower_pos (separated label))
    (holder_inverse_bound density lower_pos separated)
    (fun label => by dsimp only; rw [PeriodicHolderHalf.periodic density label])

theorem holderInverse_value (density : PeriodicHolderHalf) {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ label : ℝ, lower ≤ ‖density.val.1 label‖) (label : ℝ) :
    (holderInverse density lower_pos separated).val.1 label = (density.val.1 label)⁻¹ := rfl

end

end EulerNonuniqueness.Paper
