import Mathlib

open Set Metric

namespace EulerNonuniqueness.General

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]

theorem hasDerivAt_of_analyticAt {function : ℂ → Target} {point : ℂ}
    (analytic : AnalyticAt ℂ function point) : HasDerivAt function (deriv function point) point :=
  analytic.differentiableAt.hasDerivAt

theorem diffContOnCl_of_differentiableAt_closedBall {function : ℂ → Target}
    {center : ℂ} {radius : ℝ} (positive : 0 < radius)
    (differentiable : ∀ point ∈ closedBall center radius, DifferentiableAt ℂ function point) :
    DiffContOnCl ℂ function (ball center radius) := by
  constructor
  · intro point inside
    exact (differentiable point (ball_subset_closedBall inside)).differentiableWithinAt
  · rw [closure_ball center positive.ne']
    intro point inside
    exact (differentiable point inside).continuousAt.continuousWithinAt

end EulerNonuniqueness.General
