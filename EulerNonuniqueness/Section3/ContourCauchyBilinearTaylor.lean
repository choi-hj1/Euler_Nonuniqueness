import EulerNonuniqueness.Section3.ContourQuadraticCoefficientIdentity
import EulerNonuniqueness.Section3.ContourSecondVariationBound

open Set Metric
open scoped NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem contourCauchySecondVariation_smul_right
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℂ) :
    contourCauchySecondVariation data first (scalar • second) density =
      scalar • contourCauchySecondVariation data first second density := by
  rw [contourCauchySecondVariation_symm data first (scalar • second) density small,
    contourCauchySecondVariation_smul_left data second first density small,
    contourCauchySecondVariation_symm data second first density small]

theorem contourCauchy_bilinear_line_cubic_remainder_bound
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
        parameter ^ 2 • ((1 / 2 : ℂ) •
          contourCauchySecondVariation data direction direction density)‖ ≤
      (2 * (contourCauchyUniformOperatorConstant radius * ‖density‖) /
        (parameterRadius : ℝ) ^ 3) * ‖parameter‖ ^ 3 := by
  have coefficient := contourCauchyQuadraticCoefficient_eq_secondVariation data direction density
    nonnegative small positive nearby
  have half_coefficient : contourCauchyQuadraticCoefficient data direction density parameterRadius =
      (1 / 2 : ℂ) • contourCauchySecondVariation data direction direction density := by
    rw [← coefficient, smul_smul]
    norm_num
  rw [← half_coefficient]
  exact contourCauchy_complex_line_cubic_remainder_bound data direction density
    nonnegative small positive nearby parameter_small

end

end EulerNonuniqueness.Paper
