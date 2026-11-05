import EulerNonuniqueness.Section3.ContourVelocityAmbientThirdRegularity
import EulerNonuniqueness.Section3.ContourVelocitySecondFrechet
import EulerNonuniqueness.General.IsometricLocalSecondRegularity
import EulerNonuniqueness.General.RealOperatorCompleteness

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] velocitySecondHolderSpace velocitySecondC1Space
  velocitySecondEndGroup velocitySecondEndSpace
  velocitySecondAmbientOperatorGroup velocitySecondAmbientOperatorSpace

theorem contourVelocity_derivative_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      (fderiv ℝ extendedContourVelocity) standardCircleBanach := by
  letI : CompleteSpace PeriodicC1HolderHalf := periodicC1HolderGraph_isClosed.completeSpace_coe
  letI : CompleteSpace (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
    EulerNonuniqueness.General.completeSpace_realOperator
      (Domain := PeriodicC1HolderHalf) (Target := PeriodicC1HolderHalf)
  let embedding : (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) →ₗᵢ[ℝ]
      (PeriodicC1HolderHalf →L[ℝ] C1HolderGraphAmbient) := by
    with_reducible_and_instances
      exact closedSubmoduleOperatorEmbedding (domain := PeriodicC1HolderHalf)
        (ambient := C1HolderGraphAmbient) periodicC1HolderGraph
  have equal : (fun data => embedding (fderiv ℝ extendedContourVelocity data))
      =ᶠ[𝓝 standardCircleBanach]
      fderiv ℝ (fun data : PeriodicC1HolderHalf => (extendedContourVelocity data).val) := by
    have positive : 0 < min 1 (2 / (3 * Real.pi)) := by positivity
    filter_upwards [ball_mem_nhds standardCircleBanach positive] with data inside
    have small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
      with_reducible_and_instances
        simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using inside
    exact closedSubmoduleOperatorEmbedding_fderiv periodicC1HolderGraph
      (differentiableAt_extendedContourVelocity data small)
  have ambient := contourVelocityAmbient_derivative_hasLipschitzSecondDerivativeNear
  have image := ambient.congr equal
  exact EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_of_linearIsometry_comp
    embedding image

end

end EulerNonuniqueness.Paper
