import EulerNonuniqueness.General.TwiceDifferentiableOperations
import EulerNonuniqueness.General.AnalyticSecondDifferentiability

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

variable {Domain Value : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]

theorem twice_differentiable_pullback_of_analytic_coefficients
    (field : Value → Value) (chart : Domain → Value)
    (coefficient : Domain → Value →L[ℝ] Value) (base : Domain)
    (firstField : ∀ᶠ point in 𝓝 (chart base), DifferentiableAt ℝ field point)
    (secondField : DifferentiableAt ℝ (fderiv ℝ field) (chart base))
    (chartAnalytic : AnalyticAt ℝ chart base) (coefficientAnalytic : AnalyticAt ℝ coefficient base) :
    DifferentiableAt ℝ (fun point => coefficient point (field (chart point))) base ∧
    DifferentiableAt ℝ (fderiv ℝ (fun point => coefficient point (field (chart point)))) base := by
  have firstChart : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ chart point :=
    chartAnalytic.eventually_analyticAt.mono (fun _ actual => actual.differentiableAt)
  have firstCoefficient : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ coefficient point :=
    coefficientAnalytic.eventually_analyticAt.mono (fun _ actual => actual.differentiableAt)
  have secondChart := differentiableAt_fderiv_of_analyticAt chart base chartAnalytic
  have secondCoefficient := differentiableAt_fderiv_of_analyticAt coefficient base coefficientAnalytic
  refine ⟨coefficientAnalytic.differentiableAt.clm_apply
    (firstField.self_of_nhds.comp base chartAnalytic.differentiableAt), ?_⟩
  exact differentiableAt_fderiv_pullback field chart coefficient base firstField firstChart firstCoefficient
    secondField secondChart secondCoefficient

end

end EulerNonuniqueness.General
