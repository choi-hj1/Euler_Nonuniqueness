import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem second_derivative_symmetric_on_ball
    (function : Domain → Target) (first : Domain → Domain →L[ℝ] Target)
    (second : Domain → Domain →L[ℝ] Domain →L[ℝ] Target)
    (center : Domain) {radius : ℝ}
    (actualFirst : ∀ value ∈ closedBall center radius, HasFDerivAt function (first value) value)
    (actualSecond : ∀ value ∈ closedBall center radius, HasFDerivAt first (second value) value)
    (base : Domain) (inside : base ∈ ball center radius) (left right : Domain) :
    second base left right = second base right left := by
  have nearby : ∀ᶠ value in 𝓝 base, HasFDerivAt function (first value) value := by
    filter_upwards [isOpen_ball.mem_nhds inside] with value member
    exact actualFirst value (ball_subset_closedBall member)
  exact second_derivative_symmetric_of_eventually_of_real nearby
    (actualSecond base (ball_subset_closedBall inside)) left right

end

end EulerNonuniqueness.General
