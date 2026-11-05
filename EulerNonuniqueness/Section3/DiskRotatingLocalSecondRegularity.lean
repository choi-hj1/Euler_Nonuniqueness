import EulerNonuniqueness.Section3.ContourVelocityLocalSecondRegularity
import EulerNonuniqueness.Section3.DiskRotatingSecondFrechet
import EulerNonuniqueness.General.LocalSecondLipschitzCalculus

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace

theorem diskEulerRotatingField_derivative_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fderiv ℝ diskEulerRotatingField) standardCircleBanach := by
  let rotation : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf := c1ProductCLM (c1Constant (Complex.I / 2))
  have regular := contourVelocity_derivative_hasLipschitzDerivativeNear.sub
    (EulerNonuniqueness.General.hasLipschitzDerivativeNear_const rotation standardCircleBanach)
  apply regular.congr
  have threshold : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  filter_upwards [ball_mem_nhds standardCircleBanach threshold] with data member
  have actual := differentiableAt_extendedContourVelocity data
    (by simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using member)
  change fderiv ℝ (fun point => extendedContourVelocity point - rotation point) data = _
  with_reducible
    exact (actual.hasFDerivAt.sub (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
      (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) rotation)).fderiv

end EulerNonuniqueness.Paper
