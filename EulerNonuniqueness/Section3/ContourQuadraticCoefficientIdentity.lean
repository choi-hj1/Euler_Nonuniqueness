import EulerNonuniqueness.Section3.CauchyQuadraticDerivative
import EulerNonuniqueness.Section3.ContourCauchyCubicRemainder
import EulerNonuniqueness.Section3.ContourCauchySecondVariation

open Set Metric Filter
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem contourCauchy_complex_line_hasDerivAt (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) (parameter : ℂ)
    (small : ‖data + parameter • direction - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    HasDerivAt (fun current : ℂ => extendedContourCauchy (data + current • direction) density)
      (contourCauchyDirectionalDerivative (data + parameter • direction) direction density)
      parameter := by
  have actual := contourCauchyDirectionalDerivative_hasDerivAt
    (data + parameter • direction) direction density small
  have outer : HasDerivAt (fun current : ℂ =>
      extendedContourCauchy (data + parameter • direction + current • direction) density)
      (contourCauchyDirectionalDerivative (data + parameter • direction) direction density)
      (parameter - parameter) := by simpa only [sub_self] using actual
  have inner := (hasDerivAt_id parameter).sub_const parameter
  have translated := outer.scomp (h := fun current : ℂ => current - parameter) parameter inner
  simp only [one_smul] at translated
  apply translated.congr_of_eventuallyEq
  filter_upwards [] with current
  dsimp only [Function.comp_apply]
  have identity : data + parameter • direction + (current - parameter) • direction =
      data + current • direction := by
    rw [sub_smul current parameter direction]
    abel
  rw [identity]

theorem contourCauchyQuadraticCoefficient_eq_secondVariation
    (data direction : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {radius : ℝ} (nonnegative : 0 ≤ radius)
    (small : radius < min 1 (2 / (3 * Real.pi)))
    {parameterRadius : ℝ≥0} (positive : 0 < parameterRadius)
    (nearby : ∀ parameter ∈ closedBall (0 : ℂ) parameterRadius,
      ‖data + parameter • direction - standardCircleBanach‖ ≤ radius) :
    (2 : ℂ) • contourCauchyQuadraticCoefficient data direction density parameterRadius =
      contourCauchySecondVariation data direction direction density := by
  have continuous := extendedContourCauchy_continuousOn_complex_line data direction density
    nonnegative small nearby
  have holomorphic : DiffContOnCl ℂ
      (fun current : ℂ => extendedContourCauchy (data + current • direction) density)
      (ball 0 parameterRadius) := by
    apply DiffContOnCl.mk_ball _ continuous
    intro current member
    exact (extendedContourCauchy_differentiableAt_complex_line data direction density current
      ((nearby current (ball_subset_closedBall member)).trans_lt small)).differentiableWithinAt
  have coefficient := cauchyQuadraticCoefficient_second_derivative positive holomorphic
  have initial_small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    simpa only [zero_smul, add_zero] using
      (nearby 0 (mem_closedBall_self parameterRadius.coe_nonneg)).trans_lt small
  have derivative := contourCauchySecondVariation_hasDerivAt data direction direction density initial_small
  have derivative_equality :
      (fun parameter : ℂ => contourCauchyDirectionalDerivative
        (data + parameter • direction) direction density) =ᶠ[𝓝 0]
      deriv (fun current : ℂ => extendedContourCauchy (data + current • direction) density) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) positive] with parameter member
    exact (contourCauchy_complex_line_hasDerivAt data direction density parameter
      ((nearby parameter (ball_subset_closedBall member)).trans_lt small)).deriv.symm
  exact coefficient.trans ((derivative.congr_of_eventuallyEq derivative_equality.symm).deriv)

end

end EulerNonuniqueness.Paper
