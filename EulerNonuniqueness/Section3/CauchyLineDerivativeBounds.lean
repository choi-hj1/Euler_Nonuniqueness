import EulerNonuniqueness.Section3.CauchyDerivativeDifference

open Set Metric
open scoped NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target] [CompleteSpace Target]

theorem cauchy_derivative_norm_bound_of_increment_bound
    {function : ℂ → Target} {radius : ℝ≥0} (positive : 0 < radius)
    (holomorphic : DiffContOnCl ℂ function (ball 0 radius)) {constant : ℝ}
    (bounded : ∀ parameter ∈ sphere (0 : ℂ) radius,
      ‖function parameter - function 0‖ ≤ constant * (radius : ℝ)) :
    ‖deriv function 0‖ ≤ constant := by
  have constantHolomorphic : DiffContOnCl ℂ (fun _ : ℂ => function 0) (ball 0 radius) :=
    ⟨differentiableOn_const (function 0), continuousOn_const⟩
  have estimate := cauchy_derivative_difference_bound positive holomorphic constantHolomorphic bounded
  rw [deriv_const, sub_zero] at estimate
  exact estimate.trans_eq (by field_simp)

theorem cauchy_quadratic_remainder_bound_of_increment_bound
    {function : ℂ → Target} {radius : ℝ≥0} (positive : 0 < radius)
    (holomorphic : DiffContOnCl ℂ function (ball 0 radius)) {constant : ℝ}
    (bounded : ∀ parameter ∈ sphere (0 : ℂ) radius,
      ‖function parameter - function 0‖ ≤ constant * (radius : ℝ))
    {position : ℂ} (nearby : 2 * ‖position‖ ≤ radius) :
    ‖function position - function 0 - position • deriv function 0‖ ≤
      (2 * constant / (radius : ℝ)) * ‖position‖ ^ 2 := by
  have shiftedHolomorphic : DiffContOnCl ℂ (fun parameter => function parameter - function 0)
      (ball 0 radius) := holomorphic.sub ⟨differentiableOn_const (function 0), continuousOn_const⟩
  have derivative : deriv (fun parameter : ℂ => function parameter - function 0) 0 = deriv function 0 := by
    have actual := ((holomorphic.differentiableOn 0 (mem_ball_self positive)).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self positive))).hasDerivAt.sub_const (function 0)
    exact actual.deriv
  have estimate := cauchy_first_remainder_bound positive shiftedHolomorphic nearby bounded
  rw [derivative, sub_self, sub_zero] at estimate
  exact estimate.trans_eq (by
    have nonzero : (radius : ℝ) ≠ 0 := ne_of_gt positive
    field_simp
    ring)

end

end EulerNonuniqueness.Paper
