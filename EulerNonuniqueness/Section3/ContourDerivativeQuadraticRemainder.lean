import EulerNonuniqueness.Section3.ContourDerivativeLineRemainder
import EulerNonuniqueness.Section3.ContourCauchyBilinearTaylor

open Set Metric
open scoped NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem contourCauchyDerivative_quadratic_remainder_bound
    (data first increment : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (increment_small : ‖increment‖ ≤ (innerRadius - ‖data - standardCircleBanach‖) / 4) :
    ‖contourCauchyDirectionalDerivative (data + increment) first density -
      contourCauchyDirectionalDerivative data first density -
      contourCauchySecondVariation data first increment density‖ ≤
      (8 * contourCauchyParameterOperatorConstant outerRadius * ‖density‖ /
        (innerRadius - ‖data - standardCircleBanach‖) ^ 2) * ‖first‖ * ‖increment‖ ^ 2 := by
  have data_small := near.trans (gap.trans small)
  by_cases zero : increment = 0
  · subst increment
    have variation_zero : contourCauchySecondVariation data first 0 density = 0 := by
      have actual := contourCauchySecondVariation_smul_right data first 0 density data_small (0 : ℂ)
      simpa only [zero_smul] using actual
    have input_zero_norm : ‖(0 : PeriodicC1HolderHalf)‖ = 0 := by
      simpa only [zero_smul, norm_zero, zero_mul] using norm_smul (0 : ℂ) data
    rw [input_zero_norm] at increment_small ⊢
    simp only [add_zero, sub_self, variation_zero, sub_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, le_refl]
  have increment_positive : 0 < ‖increment‖ := (norm_pos_iff (a := increment)).mpr zero
  have scalar_nonzero : (‖increment‖ : ℂ) ≠ 0 := by exact_mod_cast increment_positive.ne'
  let direction : PeriodicC1HolderHalf := (‖increment‖ : ℂ)⁻¹ • increment
  have direction_norm : ‖direction‖ = 1 := by
    dsimp only [direction]
    rw [norm_smul (‖increment‖ : ℂ)⁻¹ increment, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos increment_positive, inv_mul_cancel₀ increment_positive.ne']
  have restoration : (‖increment‖ : ℂ) • direction = increment := by
    dsimp only [direction]
    rw [smul_smul, mul_inv_cancel₀ scalar_nonzero, one_smul]
  let parameterRadius : ℝ≥0 := ⟨(innerRadius - ‖data - standardCircleBanach‖) / 2, by linarith⟩
  have positive : 0 < parameterRadius := by change 0 < (innerRadius - ‖data - standardCircleBanach‖) / 2; linarith
  have nearby (parameter : ℂ) (member : parameter ∈ closedBall (0 : ℂ) parameterRadius) :
      ‖data + parameter • direction - standardCircleBanach‖ ≤ innerRadius := by
    have parameter_bound : ‖parameter‖ ≤ (innerRadius - ‖data - standardCircleBanach‖) / 2 := by
      simpa only [mem_closedBall, dist_zero_right] using member
    exact (complexContourPerturbation_distance data direction parameter).trans
      (by rw [direction_norm, mul_one]; linarith)
  have parameter_small : 2 * ‖(‖increment‖ : ℂ)‖ ≤ parameterRadius := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos increment_positive]
    change 2 * ‖increment‖ ≤ (innerRadius - ‖data - standardCircleBanach‖) / 2
    linarith
  have estimate := contourCauchyDerivative_complex_line_remainder_bound data first direction density
    ((norm_nonneg _).trans near.le) gap small positive nearby parameter_small
  rw [restoration, ← contourCauchySecondVariation_smul_right data first direction density data_small,
    restoration] at estimate
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos increment_positive] at estimate
  apply estimate.trans_eq
  change (2 * (contourCauchyParameterOperatorConstant outerRadius * ‖density‖ * ‖first‖) /
      ((innerRadius - ‖data - standardCircleBanach‖) / 2) ^ 2) * ‖increment‖ ^ 2 = _
  field_simp
  ring

end

end EulerNonuniqueness.Paper
