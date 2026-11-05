import Mathlib

namespace EulerNonuniqueness.General

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range] [CompleteSpace Range]

theorem differentiableAt_fderiv_of_analyticAt
    (function : Domain → Range) (base : Domain) (analytic : AnalyticAt ℝ function base) :
    DifferentiableAt ℝ (fderiv ℝ function) base := by
  have smooth : ContDiffAt ℝ 2 function base := analytic.contDiffAt
  have derivativeSmooth : ContDiffAt ℝ 1 (fderiv ℝ function) base := smooth.fderiv_right (by norm_num)
  exact derivativeSmooth.differentiableAt (by decide)

end EulerNonuniqueness.General
