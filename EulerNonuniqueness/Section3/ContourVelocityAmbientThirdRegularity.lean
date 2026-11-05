import EulerNonuniqueness.Section3.ContourVelocityValueThirdRegularity
import EulerNonuniqueness.Section3.ContourVelocityTangentThirdRegularity
import EulerNonuniqueness.Section3.ContourVelocityAmbientHigherDerivative

open Filter Metric
open scoped Topology BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] ambientHigherHolderSpace ambientHigherC1Space
  ambientHigherHolderOperatorGroup ambientHigherHolderOperatorSpace
  ambientHigherValueOperatorGroup ambientHigherValueOperatorSpace
  ambientHigherOperatorGroup ambientHigherOperatorSpace

theorem extendedContourVelocityAmbientDerivativeCLM_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      extendedContourVelocityAmbientDerivativeCLM standardCircleBanach := by
  let postcomposition := ContinuousLinearMap.compL ℝ PeriodicC1HolderHalf
    PeriodicHolderHalf (ℝ →ᵇ ℂ) holderValueFunctionRealCLM
  have value := extendedContourVelocityHolderDerivativeCLM_hasLipschitzSecondDerivativeNear.map
    postcomposition
  have paired := value.prodMk extendedContourVelocityTangentDerivativeCLM_hasLipschitzSecondDerivativeNear
  let product := (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := ℝ →ᵇ ℂ) (G := PeriodicHolderHalf) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  exact paired.map product

theorem contourVelocityAmbient_derivative_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      (fderiv ℝ (fun data : PeriodicC1HolderHalf => (extendedContourVelocity data).val))
      standardCircleBanach := by
  apply extendedContourVelocityAmbientDerivativeCLM_hasLipschitzSecondDerivativeNear.congr
  let radius := min 1 (2 / (3 * Real.pi)) / 2
  have positive : 0 < radius := by dsimp only [radius]; positivity
  have small : radius < min 1 (2 / (3 * Real.pi)) := by
    dsimp only [radius]
    have threshold : 0 < min 1 (2 / (3 * Real.pi)) := by positivity
    linarith
  filter_upwards [ball_mem_nhds standardCircleBanach positive] with data inside
  have near : ‖data - standardCircleBanach‖ < radius := by
    with_reducible_and_instances
      simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using inside
  rw [HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := C1HolderGraphAmbient)
    (hasFDerivAt_contourVelocityAmbient data near small),
    extendedContourVelocityAmbientDerivativeCLM_eq data near small]

end

end EulerNonuniqueness.Paper
