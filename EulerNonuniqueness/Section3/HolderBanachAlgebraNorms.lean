import EulerNonuniqueness.Section3.HolderBanachAlgebra
import EulerNonuniqueness.Section3.HolderNormCharacterization

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem holderProduct_norm_bound (first second : PeriodicHolderHalf) :
    ‖holderProduct first second‖ ≤ 2 * ‖first‖ * ‖second‖ := by
  apply PeriodicHolderHalf.norm_le_of_bounds _ (by positivity)
  · intro label
    rw [holderProduct_value, norm_mul]
    have estimate := mul_le_mul (PeriodicHolderHalf.value_bound first label) (PeriodicHolderHalf.value_bound second label)
      (norm_nonneg _) (norm_nonneg _)
    nlinarith [mul_nonneg (norm_nonneg first) (norm_nonneg second)]
  · exact holder_product_bound first second

theorem holderConjugate_norm_bound (density : PeriodicHolderHalf) : ‖holderConjugate density‖ ≤ ‖density‖ := by
  apply PeriodicHolderHalf.norm_le_of_bounds _ (norm_nonneg _)
  · intro label
    rw [holderConjugate_value, norm_star]
    exact PeriodicHolderHalf.value_bound density label
  · intro first second
    rw [holderConjugate_value, holderConjugate_value, ← star_sub, norm_star]
    exact PeriodicHolderHalf.holder_bound density first second

theorem holderComplexMul_norm_bound (scalar : ℂ) (density : PeriodicHolderHalf) :
    ‖holderComplexMul scalar density‖ ≤ ‖scalar‖ * ‖density‖ := by
  apply PeriodicHolderHalf.norm_le_of_bounds _ (by positivity)
  · intro label
    rw [holderComplexMul_value, norm_mul]
    exact mul_le_mul_of_nonneg_left (PeriodicHolderHalf.value_bound density label) (norm_nonneg _)
  · intro first second
    rw [holderComplexMul_value, holderComplexMul_value, ← mul_sub, norm_mul]
    exact (mul_le_mul_of_nonneg_left (PeriodicHolderHalf.holder_bound density first second)
      (norm_nonneg _)).trans_eq (by ring)

theorem holderInverse_norm_bound (density : PeriodicHolderHalf) {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ label : ℝ, lower ≤ ‖density.val.1 label‖) :
    ‖holderInverse density lower_pos separated‖ ≤ max (1 / lower) (‖density‖ / lower ^ 2) := by
  apply PeriodicHolderHalf.norm_le_of_bounds _ (by positivity)
  · intro label
    rw [holderInverse_value, norm_inv]
    have estimate : ‖density.val.1 label‖⁻¹ ≤ 1 / lower := by
      simpa only [one_div] using inv_anti₀ lower_pos (separated label)
    exact estimate.trans (le_max_left _ _)
  · intro first second
    rw [holderInverse_value, holderInverse_value]
    exact (holder_inverse_bound density lower_pos separated first second).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))

theorem holderInverse_eq_of_lower (density : PeriodicHolderHalf) {firstLower secondLower : ℝ}
    (first_pos : 0 < firstLower) (second_pos : 0 < secondLower)
    (first_separated : ∀ label : ℝ, firstLower ≤ ‖density.val.1 label‖)
    (second_separated : ∀ label : ℝ, secondLower ≤ ‖density.val.1 label‖) :
    holderInverse density first_pos first_separated = holderInverse density second_pos second_separated := by
  apply PeriodicHolderHalf.ext_value
  intro label
  rfl

theorem holderProduct_difference (firstLeft firstRight secondLeft secondRight : PeriodicHolderHalf) :
    holderProduct firstLeft firstRight - holderProduct secondLeft secondRight =
      holderProduct (firstLeft - secondLeft) firstRight + holderProduct secondLeft (firstRight - secondRight) := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change firstLeft.val.1 label * firstRight.val.1 label - secondLeft.val.1 label * secondRight.val.1 label =
    (firstLeft.val.1 label - secondLeft.val.1 label) * firstRight.val.1 label +
      secondLeft.val.1 label * (firstRight.val.1 label - secondRight.val.1 label)
  ring

theorem holderProduct_difference_norm_bound (firstLeft firstRight secondLeft secondRight : PeriodicHolderHalf) :
    ‖holderProduct firstLeft firstRight - holderProduct secondLeft secondRight‖ ≤
      2 * ‖firstLeft - secondLeft‖ * ‖firstRight‖ + 2 * ‖secondLeft‖ * ‖firstRight - secondRight‖ := by
  rw [holderProduct_difference]
  exact (norm_add_le _ _).trans (add_le_add (holderProduct_norm_bound _ _) (holderProduct_norm_bound _ _))

theorem holderConjugate_sub (first second : PeriodicHolderHalf) :
    holderConjugate first - holderConjugate second = holderConjugate (first - second) := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change star (first.val.1 label) - star (second.val.1 label) = star (first.val.1 label - second.val.1 label)
  exact (star_sub _ _).symm

theorem holderConjugate_difference_norm_bound (first second : PeriodicHolderHalf) :
    ‖holderConjugate first - holderConjugate second‖ ≤ ‖first - second‖ := by
  rw [holderConjugate_sub]
  exact holderConjugate_norm_bound _

theorem holderComplexMul_sub (scalar : ℂ) (first second : PeriodicHolderHalf) :
    holderComplexMul scalar first - holderComplexMul scalar second = holderComplexMul scalar (first - second) := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change scalar * first.val.1 label - scalar * second.val.1 label = scalar * (first.val.1 label - second.val.1 label)
  ring

theorem holderComplexMul_difference_norm_bound (scalar : ℂ) (first second : PeriodicHolderHalf) :
    ‖holderComplexMul scalar first - holderComplexMul scalar second‖ ≤ ‖scalar‖ * ‖first - second‖ := by
  rw [holderComplexMul_sub]
  exact holderComplexMul_norm_bound _ _

theorem holderInverse_difference_norm_bound (first second : PeriodicHolderHalf) {firstLower secondLower : ℝ}
    (first_pos : 0 < firstLower) (second_pos : 0 < secondLower)
    (first_separated : ∀ label : ℝ, firstLower ≤ ‖first.val.1 label‖)
    (second_separated : ∀ label : ℝ, secondLower ≤ ‖second.val.1 label‖) :
    ‖holderInverse first first_pos first_separated - holderInverse second second_pos second_separated‖ ≤
      4 * ‖first - second‖ * ‖holderInverse first first_pos first_separated‖ *
        ‖holderInverse second second_pos second_separated‖ := by
  have identity : holderInverse first first_pos first_separated - holderInverse second second_pos second_separated =
      holderProduct (second - first)
        (holderProduct (holderInverse first first_pos first_separated) (holderInverse second second_pos second_separated)) := by
    apply PeriodicHolderHalf.ext_value
    intro label
    change (first.val.1 label)⁻¹ - (second.val.1 label)⁻¹ =
      (second.val.1 label - first.val.1 label) * ((first.val.1 label)⁻¹ * (second.val.1 label)⁻¹)
    have first_ne := norm_ne_zero_iff.mp (ne_of_gt (first_pos.trans_le (first_separated label)))
    have second_ne := norm_ne_zero_iff.mp (ne_of_gt (second_pos.trans_le (second_separated label)))
    field_simp
  rw [identity]
  apply (holderProduct_norm_bound _ _).trans
  apply (mul_le_mul_of_nonneg_left (holderProduct_norm_bound _ _) (by positivity : 0 ≤ 2 * ‖second - first‖)).trans_eq
  rw [norm_sub_rev second first]
  ring

theorem PeriodicC1HolderHalf.tangent_norm_bound (data : PeriodicC1HolderHalf) : ‖data.val.2‖ ≤ ‖data‖ :=
  le_max_right _ _

theorem PeriodicC1HolderHalf.tangent_difference_norm_bound (first second : PeriodicC1HolderHalf) :
    ‖first.val.2 - second.val.2‖ ≤ ‖first - second‖ :=
  PeriodicC1HolderHalf.tangent_norm_bound (first - second)

end EulerNonuniqueness.Paper
