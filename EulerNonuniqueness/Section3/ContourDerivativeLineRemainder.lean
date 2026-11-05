import EulerNonuniqueness.Section3.ContourDerivativeLineHolomorphic
import EulerNonuniqueness.Section3.CauchyTaylorRemainder

open Set Metric
open scoped NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem contourCauchyDerivative_complex_line_remainder_bound
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    {parameterRadius : ℝ≥0} (positive : 0 < parameterRadius)
    (nearby : ∀ parameter ∈ closedBall (0 : ℂ) parameterRadius,
      ‖data + parameter • second - standardCircleBanach‖ ≤ innerRadius)
    {parameter : ℂ} (parameter_small : 2 * ‖parameter‖ ≤ parameterRadius) :
    ‖contourCauchyDirectionalDerivative (data + parameter • second) first density -
      contourCauchyDirectionalDerivative data first density -
      parameter • contourCauchySecondVariation data first second density‖ ≤
      (2 * (contourCauchyParameterOperatorConstant outerRadius * ‖density‖ * ‖first‖) /
        (parameterRadius : ℝ) ^ 2) * ‖parameter‖ ^ 2 := by
  have holomorphic : DiffContOnCl ℂ (fun current : ℂ =>
      contourCauchyDirectionalDerivative (data + current • second) first density)
      (ball 0 parameterRadius) := by
    apply DiffContOnCl.mk_ball _
      (contourCauchyDirectionalDerivative_continuousOn_complex_line data first second density
        nonnegative gap small nearby)
    intro current member
    exact (contourCauchyDirectionalDerivative_hasDerivAt_complex_line data first second density current
      (((nearby current (ball_subset_closedBall member)).trans_lt gap).trans small)).differentiableAt.differentiableWithinAt
  have estimate := cauchy_first_remainder_bound positive holomorphic parameter_small
    (fun current member => contourCauchyDirectionalDerivative_norm_bound
      (data + current • second) first density
      ((nearby current (sphere_subset_closedBall member)).trans_lt gap) small)
  simpa only [zero_smul, add_zero, contourCauchySecondVariation] using estimate

end

end EulerNonuniqueness.Paper
