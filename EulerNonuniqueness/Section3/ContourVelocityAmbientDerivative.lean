import EulerNonuniqueness.Section3.ContourVelocityTangentFrechet
import EulerNonuniqueness.Section3.ContourVelocityDerivativeValue

open Set Metric Filter
open scoped Topology BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance velocityAmbientDerivativeHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance velocityAmbientDerivativeC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

def contourVelocityAmbientDerivativeCLM (data : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) : PeriodicC1HolderHalf →L[ℝ] C1HolderGraphAmbient :=
  (holderValueFunctionRealCLM.comp (contourVelocityHolderDerivativeCLM data near small)).prod
    (contourVelocityTangentDerivativeCLM data near small)

theorem hasFDerivAt_contourVelocityAmbient (data : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt (fun current : PeriodicC1HolderHalf => (extendedContourVelocity current).val)
      (contourVelocityAmbientDerivativeCLM data near small) data := by
  have holder : HasFDerivAt holderContourVelocity (contourVelocityHolderDerivativeCLM data near small) data := by
    exact hasFDerivAt_holderContourVelocity data near small
  have value : HasFDerivAt (fun current : PeriodicC1HolderHalf => (holderContourVelocity current).val.1)
      (holderValueFunctionRealCLM.comp (contourVelocityHolderDerivativeCLM data near small)) data := by
    exact HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
      (G := ℝ →ᵇ ℂ) (f := holderContourVelocity) (g := fun density : PeriodicHolderHalf => density.val.1)
      data (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicHolderHalf)
        (F := ℝ →ᵇ ℂ) holderValueFunctionRealCLM) holder
  have tangent : HasFDerivAt holderContourVelocityTangent
      (contourVelocityTangentDerivativeCLM data near small) data := by
    exact hasFDerivAt_holderContourVelocityTangent data near small
  have pair : HasFDerivAt (fun current : PeriodicC1HolderHalf =>
      ((holderContourVelocity current).val.1, holderContourVelocityTangent current))
      (contourVelocityAmbientDerivativeCLM data near small) data := by
    exact HasFDerivAt.prodMk (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := ℝ →ᵇ ℂ) (G := PeriodicHolderHalf) value tangent
  have equality : (fun current : PeriodicC1HolderHalf => (extendedContourVelocity current).val) =ᶠ[𝓝 data]
      (fun current : PeriodicC1HolderHalf => ((holderContourVelocity current).val.1,
        holderContourVelocityTangent current)) := by
    have positive : 0 < radius - ‖data - standardCircleBanach‖ := sub_pos.mpr near
    filter_upwards [Metric.ball_mem_nhds data positive] with current member
    rw [mem_ball, dist_eq_norm current data] at member
    have triangle := dist_triangle current data standardCircleBanach
    rw [dist_eq_norm current standardCircleBanach, dist_eq_norm current data,
      dist_eq_norm data standardCircleBanach] at triangle
    have current_small : ‖current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by linarith
    exact extendedContourVelocity_ambient_eq current current_small
  exact HasFDerivAt.congr_of_eventuallyEq (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := C1HolderGraphAmbient) pair equality

theorem contourVelocityAmbientDerivative_mem (data increment : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    contourVelocityAmbientDerivativeCLM data near small increment ∈ periodicC1HolderGraph :=
  closedSubmodule_derivative_mem periodicC1HolderGraph periodicC1HolderGraph_isClosed
    (hasFDerivAt_contourVelocityAmbient data near small) increment

end

end EulerNonuniqueness.Paper
