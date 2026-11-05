import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic

open Set Metric Complex Filter
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem cauchy_hasDerivAt_center {function : ℂ → E} {radius : ℝ≥0} (positive : 0 < radius)
    (holomorphic : DiffContOnCl ℂ function (ball 0 radius)) :
    HasDerivAt function ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ parameter in C(0, radius), parameter⁻¹ • parameter⁻¹ • function parameter) 0 := by
  have integrable : CircleIntegrable function 0 radius :=
    ContinuousOn.circleIntegrable radius.coe_nonneg
      (holomorphic.continuousOn_ball.mono sphere_subset_closedBall)
  have series := (hasFPowerSeriesOn_cauchy_integral integrable positive).hasFPowerSeriesAt.hasFDerivAt.hasDerivAt
  have equality : (fun position => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ parameter in C(0, radius), (parameter - position)⁻¹ • function parameter) =ᶠ[𝓝 0] function := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) positive] with position member
    exact holomorphic.two_pi_i_inv_smul_circleIntegral_sub_inv_smul member
  have derivative := series.congr_of_eventuallyEq equality.symm
  simp only [continuousMultilinearCurryFin1_apply, cauchyPowerSeries,
    ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_univ_one, pow_one, sub_zero] at derivative
  convert derivative using 1
  change _ = (1 : ℂ) • _
  rw [one_smul]

omit [CompleteSpace E] in
theorem cauchy_kernel_circleIntegrable {function : ℂ → E} {radius : ℝ} (positive : 0 < radius)
    (continuous : ContinuousOn function (closedBall 0 radius)) {position : ℂ}
    (inside : position ∈ ball 0 radius) (degree : ℕ) :
    CircleIntegrable (fun parameter => (parameter - position)⁻¹ ^ degree • function parameter) 0 radius := by
  apply ContinuousOn.circleIntegrable positive.le
  refine (((continuousOn_id.sub continuousOn_const).inv₀ ?_).pow degree).smul
    (continuous.mono sphere_subset_closedBall)
  intro parameter member
  apply sub_ne_zero.mpr
  intro equal
  change parameter = position at equal
  subst parameter
  exact (mem_ball.mp inside).ne (mem_sphere.mp member)

theorem cauchy_first_remainder_identity {function : ℂ → E} {radius : ℝ≥0} (positive : 0 < radius)
    (holomorphic : DiffContOnCl ℂ function (ball 0 radius)) {position : ℂ}
    (inside : position ∈ ball 0 radius) :
    function position - function 0 - position • deriv function 0 =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ parameter in C(0, radius),
        ((parameter - position)⁻¹ - parameter⁻¹ - position * (parameter⁻¹ * parameter⁻¹)) • function parameter := by
  have zero_inside : (0 : ℂ) ∈ ball 0 (radius : ℝ) := mem_ball_self positive
  have first := cauchy_kernel_circleIntegrable (function := function) (radius := (radius : ℝ))
    (position := position) (show (0 : ℝ) < radius from positive)
    holomorphic.continuousOn_ball inside 1
  have second := cauchy_kernel_circleIntegrable (function := function) (radius := (radius : ℝ))
    (position := 0) (show (0 : ℝ) < radius from positive)
    holomorphic.continuousOn_ball zero_inside 1
  have third := cauchy_kernel_circleIntegrable (function := function) (radius := (radius : ℝ))
    (position := 0) (show (0 : ℝ) < radius from positive)
    holomorphic.continuousOn_ball zero_inside 2
  simp only [pow_one, sub_zero] at first second third
  have third_integrable : CircleIntegrable (fun parameter : ℂ => position • (parameter⁻¹ • parameter⁻¹ • function parameter))
      0 radius := by simpa only [CircleIntegrable, pow_two, mul_smul] using third.smul position
  have first_sub : CircleIntegrable (fun parameter => (parameter - position)⁻¹ • function parameter -
      parameter⁻¹ • function parameter) 0 radius := first.sub second
  have integral_identity := circleIntegral.integral_sub
    (f := fun parameter => (parameter - position)⁻¹ • function parameter - parameter⁻¹ • function parameter)
    (g := fun parameter => position • (parameter⁻¹ • parameter⁻¹ • function parameter)) first_sub third_integrable
  rw [circleIntegral.integral_sub first second, circleIntegral.integral_smul] at integral_identity
  have first_formula := holomorphic.two_pi_i_inv_smul_circleIntegral_sub_inv_smul inside
  have zero_formula := holomorphic.two_pi_i_inv_smul_circleIntegral_sub_inv_smul zero_inside
  simp only [sub_zero] at zero_formula
  rw [← first_formula, ← zero_formula, (cauchy_hasDerivAt_center positive holomorphic).deriv]
  rw [smul_comm position (2 * Real.pi * Complex.I : ℂ)⁻¹, ← smul_sub, ← smul_sub,
    ← integral_identity]
  congr 1
  apply circleIntegral.integral_congr radius.coe_nonneg
  intro parameter _
  simp only [sub_smul, mul_smul]

theorem cauchy_first_remainder_bound {function : ℂ → E} {radius : ℝ≥0} (positive : 0 < radius)
    (holomorphic : DiffContOnCl ℂ function (ball 0 radius)) {position : ℂ}
    (nearby : 2 * ‖position‖ ≤ radius) {bound : ℝ}
    (bounded : ∀ parameter ∈ sphere (0 : ℂ) radius, ‖function parameter‖ ≤ bound) :
    ‖function position - function 0 - position • deriv function 0‖ ≤
      (2 * bound / (radius : ℝ) ^ 2) * ‖position‖ ^ 2 := by
  have radius_positive : (0 : ℝ) < radius := positive
  have position_inside : position ∈ ball (0 : ℂ) radius := by
    rw [mem_ball, dist_zero_right]
    nlinarith [norm_nonneg position]
  rw [cauchy_first_remainder_identity positive holomorphic position_inside]
  have estimate := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (c := 0) radius.coe_nonneg (f := fun parameter =>
      ((parameter - position)⁻¹ - parameter⁻¹ - position * (parameter⁻¹ * parameter⁻¹)) • function parameter)
    (C := (‖position‖ ^ 2 / ((radius : ℝ) ^ 2 * ((radius : ℝ) / 2))) * bound) (by
      intro parameter member
      have parameter_norm : ‖parameter‖ = radius := by simpa only [mem_sphere, dist_zero_right] using member
      have difference_lower : (radius : ℝ) / 2 ≤ ‖parameter - position‖ := by
        have reverse := norm_sub_norm_le parameter position
        rw [parameter_norm] at reverse
        linarith
      have difference_positive : 0 < ‖parameter - position‖ := lt_of_lt_of_le (by positivity) difference_lower
      have parameter_ne : parameter ≠ 0 := norm_ne_zero_iff.mp (by rw [parameter_norm]; exact radius_positive.ne')
      have difference_ne : parameter - position ≠ 0 := norm_ne_zero_iff.mp difference_positive.ne'
      have algebra : (parameter - position)⁻¹ - parameter⁻¹ - position * (parameter⁻¹ * parameter⁻¹) =
          position ^ 2 / (parameter ^ 2 * (parameter - position)) := by
        field_simp
        <;> ring
      rw [norm_smul, algebra, norm_div, norm_mul, norm_pow, norm_pow, parameter_norm]
      apply mul_le_mul _ (bounded parameter member) (norm_nonneg _) (by positivity)
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left difference_lower (sq_nonneg _)))
  exact estimate.trans_eq (by field_simp; ring)

end

end EulerNonuniqueness.Paper
