import EulerNonuniqueness.Section3.ContourCauchyBilinearTaylor

open Set Metric
open scoped NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem contourCauchy_cubic_taylor_bound (data increment : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi)))
    (increment_small : ‖increment‖ ≤ (radius - ‖data - standardCircleBanach‖) / 4) :
    ‖extendedContourCauchy (data + increment) density - extendedContourCauchy data density -
        contourCauchyDirectionalDerivative data increment density -
        (1 / 2 : ℂ) • contourCauchySecondVariation data increment increment density‖ ≤
      (16 * (contourCauchyUniformOperatorConstant radius * ‖density‖) /
        (radius - ‖data - standardCircleBanach‖) ^ 3) * ‖increment‖ ^ 3 := by
  have data_small := near.trans small
  by_cases zero : increment = 0
  · subst increment
    have derivative_zero : contourCauchyDirectionalDerivative data 0 density = 0 := by
      have actual := contourCauchyDirectionalDerivative_smul data 0 density data_small (0 : ℂ)
      simpa only [zero_smul] using actual
    have second_zero : contourCauchySecondVariation data 0 0 density = 0 := by
      have actual := contourCauchySecondVariation_smul_left data 0 0 density data_small (0 : ℂ)
      simpa only [zero_smul] using actual
    have zero_norm : ‖(0 : PeriodicC1HolderHalf)‖ = 0 := by
      simpa only [zero_smul, norm_zero, zero_mul] using norm_smul (0 : ℂ) data
    simp only [add_zero, sub_self, derivative_zero, second_zero, sub_zero, smul_zero,
      norm_zero, zero_norm, zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero, le_refl]
  have positive : 0 < ‖increment‖ := (norm_pos_iff (a := increment)).mpr zero
  have scalar_nonzero : (‖increment‖ : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  let direction : PeriodicC1HolderHalf := (‖increment‖ : ℂ)⁻¹ • increment
  have unit : ‖direction‖ = 1 := by
    dsimp only [direction]
    rw [norm_smul (‖increment‖ : ℂ)⁻¹ increment, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos positive, inv_mul_cancel₀ positive.ne']
  have restoration : (‖increment‖ : ℂ) • direction = increment := by
    dsimp only [direction]
    rw [smul_smul, mul_inv_cancel₀ scalar_nonzero, one_smul]
  let parameterRadius : ℝ≥0 := ⟨(radius - ‖data - standardCircleBanach‖) / 2,
    div_nonneg (sub_nonneg.mpr near.le) (by norm_num)⟩
  have parameter_positive : 0 < parameterRadius := by
    change 0 < (radius - ‖data - standardCircleBanach‖) / 2
    linarith
  have nearby (parameter : ℂ) (member : parameter ∈ closedBall (0 : ℂ) parameterRadius) :
      ‖data + parameter • direction - standardCircleBanach‖ ≤ radius := by
    have parameter_bound : ‖parameter‖ ≤ (radius - ‖data - standardCircleBanach‖) / 2 := by
      simpa only [mem_closedBall, dist_zero_right] using member
    have estimate := complexContourPerturbation_distance data direction parameter
    rw [unit, mul_one] at estimate
    exact estimate.trans (by linarith)
  have parameter_small : 2 * ‖(‖increment‖ : ℂ)‖ ≤ parameterRadius := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
    change 2 * ‖increment‖ ≤ (radius - ‖data - standardCircleBanach‖) / 2
    linarith
  have second_left := contourCauchySecondVariation_smul_left data direction increment density
    data_small (‖increment‖ : ℂ)
  have second_right := contourCauchySecondVariation_smul_right data direction direction density
    data_small (‖increment‖ : ℂ)
  rw [restoration] at second_left second_right
  have quadratic_identity : (‖increment‖ : ℂ) ^ 2 •
      ((1 / 2 : ℂ) • contourCauchySecondVariation data direction direction density) =
      (1 / 2 : ℂ) • contourCauchySecondVariation data increment increment density := by
    rw [second_left, second_right, smul_smul, smul_smul, smul_smul, pow_two]
    congr 1
    ring
  have estimate := contourCauchy_bilinear_line_cubic_remainder_bound data direction density
    ((norm_nonneg _).trans near.le) small parameter_positive nearby parameter_small
  rw [restoration, ← contourCauchyDirectionalDerivative_smul data direction density data_small,
    restoration, quadratic_identity, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive] at estimate
  exact estimate.trans_eq (by
    change 2 * (contourCauchyUniformOperatorConstant radius * ‖density‖) /
      ((radius - ‖data - standardCircleBanach‖) / 2) ^ 3 * ‖increment‖ ^ 3 = _
    field_simp
    ring)

end

end EulerNonuniqueness.Paper
