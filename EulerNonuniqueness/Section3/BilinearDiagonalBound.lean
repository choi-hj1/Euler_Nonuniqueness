import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear
import Mathlib.Tactic.Module

namespace EulerNonuniqueness.Paper

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem symmetricBilinear_norm_bound_of_diagonal (bilinear : E →ₗ[ℝ] E →ₗ[ℝ] F)
    (symmetric : ∀ first second, bilinear first second = bilinear second first)
    {constant : ℝ} (nonnegative : 0 ≤ constant)
    (diagonal : ∀ point, ‖bilinear point point‖ ≤ constant * ‖point‖ ^ 2)
    (first second : E) :
    ‖bilinear first second‖ ≤ (3 * constant) * ‖first‖ * ‖second‖ := by
  have unit_bound (first second : E) (first_unit : ‖first‖ = 1) (second_unit : ‖second‖ = 1) :
      ‖bilinear first second‖ ≤ 3 * constant := by
    have polarization : bilinear first second =
        (1 / 2 : ℝ) • (bilinear (first + second) (first + second) -
          bilinear first first - bilinear second second) := by
      simp only [map_add, LinearMap.add_apply, symmetric second first]
      module
    rw [polarization, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have sum_norm : ‖first + second‖ ≤ 2 := by
      simpa only [first_unit, second_unit, one_add_one_eq_two] using norm_add_le first second
    have sum_bound : ‖bilinear (first + second) (first + second)‖ ≤ 4 * constant := by
      apply (diagonal (first + second)).trans
      have squared : ‖first + second‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (first + second)]
      exact (mul_le_mul_of_nonneg_left squared nonnegative).trans_eq (by ring)
    have first_bound : ‖bilinear first first‖ ≤ constant := by simpa only [first_unit, one_pow, mul_one] using diagonal first
    have second_bound : ‖bilinear second second‖ ≤ constant := by simpa only [second_unit, one_pow, mul_one] using diagonal second
    have norm_bound :
        ‖bilinear (first + second) (first + second) - bilinear first first -
          bilinear second second‖ ≤ (4 * constant + constant) + constant :=
      (norm_sub_le _ _).trans
        (add_le_add ((norm_sub_le _ _).trans (add_le_add sum_bound first_bound)) second_bound)
    nlinarith
  by_cases first_zero : first = 0
  · subst first
    simp
  by_cases second_zero : second = 0
  · subst second
    simp
  have first_positive : 0 < ‖first‖ := norm_pos_iff.mpr first_zero
  have second_positive : 0 < ‖second‖ := norm_pos_iff.mpr second_zero
  let normalizedFirst := ‖first‖⁻¹ • first
  let normalizedSecond := ‖second‖⁻¹ • second
  have first_unit : ‖normalizedFirst‖ = 1 := by
    dsimp only [normalizedFirst]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ first_positive.ne']
  have second_unit : ‖normalizedSecond‖ = 1 := by
    dsimp only [normalizedSecond]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ second_positive.ne']
  have restore_first : ‖first‖ • normalizedFirst = first := by
    dsimp only [normalizedFirst]
    rw [smul_smul, mul_inv_cancel₀ first_positive.ne', one_smul]
  have restore_second : ‖second‖ • normalizedSecond = second := by
    dsimp only [normalizedSecond]
    rw [smul_smul, mul_inv_cancel₀ second_positive.ne', one_smul]
  have scaled : bilinear (‖first‖ • normalizedFirst) (‖second‖ • normalizedSecond) =
      (‖first‖ * ‖second‖) • bilinear normalizedFirst normalizedSecond := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm]
  rw [restore_first, restore_second] at scaled
  rw [scaled, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos first_positive second_positive)]
  exact (mul_le_mul_of_nonneg_left (unit_bound _ _ first_unit second_unit)
    (mul_nonneg first_positive.le second_positive.le)).trans_eq (by ring)

end

end EulerNonuniqueness.Paper
