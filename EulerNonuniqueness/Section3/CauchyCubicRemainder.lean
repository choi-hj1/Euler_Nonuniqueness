import EulerNonuniqueness.Section3.CauchyTaylorRemainder

open Set Metric Complex Filter
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def cauchyQuadraticCoefficient (function : ℂ → E) (radius : ℝ) : E :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∮ parameter in C(0, radius), parameter⁻¹ ^ 3 • function parameter

theorem cauchy_second_remainder_identity {function : ℂ → E} {radius : ℝ≥0}
    (positive : 0 < radius) (holomorphic : DiffContOnCl ℂ function (ball 0 radius))
    {position : ℂ} (inside : position ∈ ball 0 radius) :
    function position - function 0 - position • deriv function 0 -
        position ^ 2 • cauchyQuadraticCoefficient function radius =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ parameter in C(0, radius),
        ((parameter - position)⁻¹ - parameter⁻¹ -
          position * (parameter⁻¹ * parameter⁻¹) - position ^ 2 * parameter⁻¹ ^ 3) •
            function parameter := by
  have zero_inside : (0 : ℂ) ∈ ball 0 (radius : ℝ) := mem_ball_self positive
  have first := cauchy_kernel_circleIntegrable (function := function)
    (show (0 : ℝ) < radius from positive) holomorphic.continuousOn_ball inside 1
  have second := cauchy_kernel_circleIntegrable (function := function)
    (show (0 : ℝ) < radius from positive) holomorphic.continuousOn_ball zero_inside 1
  have third := cauchy_kernel_circleIntegrable (function := function)
    (show (0 : ℝ) < radius from positive) holomorphic.continuousOn_ball zero_inside 2
  have fourth := cauchy_kernel_circleIntegrable (function := function)
    (show (0 : ℝ) < radius from positive) holomorphic.continuousOn_ball zero_inside 3
  simp only [pow_one, sub_zero] at first second third fourth
  have remainder_integrable : CircleIntegrable (fun parameter =>
      ((parameter - position)⁻¹ - parameter⁻¹ -
        position * (parameter⁻¹ * parameter⁻¹)) • function parameter) 0 radius := by
    simpa only [sub_smul, mul_smul, pow_two] using
      (first.sub second).sub (third.smul position)
  have quadratic_integrable : CircleIntegrable (fun parameter =>
      position ^ 2 • (parameter⁻¹ ^ 3 • function parameter)) 0 radius := fourth.smul _
  have integral_identity := circleIntegral.integral_sub
    (f := fun parameter => ((parameter - position)⁻¹ - parameter⁻¹ -
      position * (parameter⁻¹ * parameter⁻¹)) • function parameter)
    (g := fun parameter => position ^ 2 • (parameter⁻¹ ^ 3 • function parameter))
    remainder_integrable quadratic_integrable
  rw [circleIntegral.integral_smul] at integral_identity
  rw [cauchy_first_remainder_identity positive holomorphic inside,
    cauchyQuadraticCoefficient, smul_comm (position ^ 2), ← smul_sub, ← integral_identity]
  congr 1
  apply circleIntegral.integral_congr radius.coe_nonneg
  intro parameter _
  simp only [sub_smul, mul_smul]

theorem cauchy_second_remainder_bound {function : ℂ → E} {radius : ℝ≥0}
    (positive : 0 < radius) (holomorphic : DiffContOnCl ℂ function (ball 0 radius))
    {position : ℂ} (nearby : 2 * ‖position‖ ≤ radius) {bound : ℝ}
    (bounded : ∀ parameter ∈ sphere (0 : ℂ) radius, ‖function parameter‖ ≤ bound) :
    ‖function position - function 0 - position • deriv function 0 -
      position ^ 2 • cauchyQuadraticCoefficient function radius‖ ≤
        (2 * bound / (radius : ℝ) ^ 3) * ‖position‖ ^ 3 := by
  have radius_positive : (0 : ℝ) < radius := positive
  have inside : position ∈ ball (0 : ℂ) radius := by
    rw [mem_ball, dist_zero_right]
    nlinarith [norm_nonneg position]
  rw [cauchy_second_remainder_identity positive holomorphic inside]
  have estimate := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (c := 0) radius.coe_nonneg (f := fun parameter =>
      ((parameter - position)⁻¹ - parameter⁻¹ - position * (parameter⁻¹ * parameter⁻¹) -
        position ^ 2 * parameter⁻¹ ^ 3) • function parameter)
    (C := (‖position‖ ^ 3 / ((radius : ℝ) ^ 3 * ((radius : ℝ) / 2))) * bound) (by
      intro parameter member
      have parameter_norm : ‖parameter‖ = radius := by
        simpa only [mem_sphere, dist_zero_right] using member
      have difference_lower : (radius : ℝ) / 2 ≤ ‖parameter - position‖ := by
        have reverse := norm_sub_norm_le parameter position
        rw [parameter_norm] at reverse
        linarith
      have difference_positive : 0 < ‖parameter - position‖ :=
        lt_of_lt_of_le (by positivity) difference_lower
      have parameter_ne : parameter ≠ 0 :=
        norm_ne_zero_iff.mp (by rw [parameter_norm]; exact radius_positive.ne')
      have difference_ne : parameter - position ≠ 0 :=
        norm_ne_zero_iff.mp difference_positive.ne'
      have algebra : (parameter - position)⁻¹ - parameter⁻¹ -
          position * (parameter⁻¹ * parameter⁻¹) - position ^ 2 * parameter⁻¹ ^ 3 =
          position ^ 3 / (parameter ^ 3 * (parameter - position)) := by
        field_simp
        <;> ring
      rw [norm_smul, algebra, norm_div, norm_mul, norm_pow, norm_pow, parameter_norm]
      apply mul_le_mul _ (bounded parameter member) (norm_nonneg _) (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left difference_lower (by positivity)))
  exact estimate.trans_eq (by field_simp; ring)

end

end EulerNonuniqueness.Paper
