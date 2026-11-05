import EulerNonuniqueness.Section3.WeakHolomorphicCurve

open Set Metric
open scoped NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

variable {Domain Target Label : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℂ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target] [CompleteSpace Target]

theorem analyticAt_operatorCurve_of_evaluations
    (evaluation : Label → Target →L[ℂ] ℂ)
    (separates : ∀ first second : Target,
      (∀ label, evaluation label first = evaluation label second) → first = second)
    {function : ℂ → Domain →L[ℂ] Target} {center : ℂ} {radius : ℝ≥0}
    (positive : 0 < radius)
    (continuous : ContinuousOn function (closedBall center radius))
    (holomorphic : ∀ direction, DifferentiableOn ℂ
      (fun parameter => function parameter direction) (ball center radius)) :
    AnalyticAt ℂ function center := by
  let operatorEvaluation : Domain × Label → (Domain →L[ℂ] Target) →L[ℂ] ℂ :=
    fun label => (evaluation label.2).comp (ContinuousLinearMap.apply ℂ Target label.1)
  apply analyticAt_of_separating_evaluations operatorEvaluation
  · intro first second equal
    apply ContinuousLinearMap.ext
    intro direction
    apply separates
    intro label
    exact equal (direction, label)
  · exact positive
  · exact continuous
  · intro label point inside
    exact (evaluation label.2).differentiableAt.comp_differentiableWithinAt point
      (holomorphic label.1 point inside)

end

end EulerNonuniqueness.Paper
