import EulerNonuniqueness.Section3.CauchyTaylorRemainder

open Set Metric Complex
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem cauchy_derivative_difference_bound {first second : ℂ → E} {radius : ℝ≥0}
    (positive : 0 < radius)
    (first_holomorphic : DiffContOnCl ℂ first (ball 0 radius))
    (second_holomorphic : DiffContOnCl ℂ second (ball 0 radius))
    {bound : ℝ} (bounded : ∀ parameter ∈ sphere (0 : ℂ) radius,
      ‖first parameter - second parameter‖ ≤ bound) :
    ‖deriv first 0 - deriv second 0‖ ≤ bound / (radius : ℝ) := by
  have first_integrable := cauchy_kernel_circleIntegrable (function := first)
    (position := 0) (show (0 : ℝ) < radius from positive)
    first_holomorphic.continuousOn_ball (mem_ball_self positive) 2
  have second_integrable := cauchy_kernel_circleIntegrable (function := second)
    (position := 0) (show (0 : ℝ) < radius from positive)
    second_holomorphic.continuousOn_ball (mem_ball_self positive) 2
  simp only [sub_zero, pow_two, mul_smul] at first_integrable second_integrable
  rw [(cauchy_hasDerivAt_center positive first_holomorphic).deriv,
    (cauchy_hasDerivAt_center positive second_holomorphic).deriv, ← smul_sub,
    ← circleIntegral.integral_sub first_integrable second_integrable]
  have estimate := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (c := 0) radius.coe_nonneg (f := fun parameter =>
      parameter⁻¹ • parameter⁻¹ • first parameter -
        parameter⁻¹ • parameter⁻¹ • second parameter)
    (C := (radius : ℝ)⁻¹ ^ 2 * bound) (by
      intro parameter member
      have parameter_norm : ‖parameter‖ = radius := by
        simpa only [mem_sphere, dist_zero_right] using member
      dsimp only
      rw [← smul_sub, ← smul_sub, norm_smul, norm_smul, norm_inv, parameter_norm]
      rw [← mul_assoc]
      exact (mul_le_mul_of_nonneg_left (bounded parameter member)
        (mul_self_nonneg (radius : ℝ)⁻¹)).trans_eq (by ring))
  exact estimate.trans_eq (by
    have radius_nonzero : (radius : ℝ) ≠ 0 := ne_of_gt positive
    field_simp
    <;> ring)

end

end EulerNonuniqueness.Paper
