import EulerNonuniqueness.Section3.ContourCauchyFrechet
import EulerNonuniqueness.Section3.CauchyCubicRemainder

open Set Metric Filter
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

def contourCauchyQuadraticCoefficient (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) (parameterRadius : ℝ) : PeriodicHolderHalf :=
  cauchyQuadraticCoefficient
    (fun parameter : ℂ => extendedContourCauchy (data + parameter • direction) density)
    parameterRadius

theorem contourCauchy_complex_line_cubic_remainder_bound
    (data direction : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {radius : ℝ} (nonnegative : 0 ≤ radius)
    (small : radius < min 1 (2 / (3 * Real.pi)))
    {parameterRadius : ℝ≥0} (positive : 0 < parameterRadius)
    (nearby : ∀ parameter ∈ closedBall (0 : ℂ) parameterRadius,
      ‖data + parameter • direction - standardCircleBanach‖ ≤ radius)
    {parameter : ℂ} (parameter_small : 2 * ‖parameter‖ ≤ parameterRadius) :
    ‖extendedContourCauchy (data + parameter • direction) density -
        extendedContourCauchy data density -
        parameter • contourCauchyDirectionalDerivative data direction density -
        parameter ^ 2 • contourCauchyQuadraticCoefficient data direction density parameterRadius‖ ≤
      (2 * (contourCauchyUniformOperatorConstant radius * ‖density‖) /
        (parameterRadius : ℝ) ^ 3) * ‖parameter‖ ^ 3 := by
  have continuous := extendedContourCauchy_continuousOn_complex_line
    data direction density nonnegative small nearby
  have holomorphic : DiffContOnCl ℂ
      (fun current : ℂ => extendedContourCauchy (data + current • direction) density)
      (ball 0 parameterRadius) := by
    apply DiffContOnCl.mk_ball _ continuous
    intro current member
    exact (extendedContourCauchy_differentiableAt_complex_line data direction density current
      ((nearby current (ball_subset_closedBall member)).trans_lt small)).differentiableWithinAt
  have estimate := cauchy_second_remainder_bound positive holomorphic parameter_small
    (fun current member => extendedContourCauchy_uniform_norm_bound _ density nonnegative small
      (nearby current (sphere_subset_closedBall member)))
  simpa only [zero_smul, add_zero, contourCauchyDirectionalDerivative,
    contourCauchyQuadraticCoefficient] using estimate

end

end EulerNonuniqueness.Paper
