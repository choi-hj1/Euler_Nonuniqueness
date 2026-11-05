import EulerNonuniqueness.Section3.ContourVelocityTangentDerivative
import EulerNonuniqueness.Section3.ClosedSubmoduleDerivative

open Set Metric Filter
open scoped Topology BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance fullVelocityHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance fullVelocityC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def holderValueFunctionRealCLM : PeriodicHolderHalf →L[ℝ] (ℝ →ᵇ ℂ) :=
  (ContinuousLinearMap.fst ℝ (ℝ →ᵇ ℂ) (HolderLabelPairs →ᵇ ℂ)).comp periodicHolderGraph.subtypeL

theorem extendedContourVelocity_ambient_eq (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    (extendedContourVelocity data).val =
      ((holderContourVelocity data).val.1, holderContourVelocityTangent data) := by
  apply Prod.ext
  · apply BoundedContinuousFunction.ext
    intro label
    rw [extendedContourVelocity_eq data small]
    exact (holderContourVelocity_value data small label).symm
  · rw [extendedContourVelocity_eq data small, contourVelocityBanach_tangent_component,
      holderContourVelocityTangent_eq data small]

theorem differentiableAt_extendedContourVelocity (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    DifferentiableAt ℝ extendedContourVelocity data := by
  obtain ⟨radius, near, radius_small⟩ := exists_between small
  have value_derivative : HasFDerivAt holderContourVelocity (contourVelocityHolderDerivativeCLM data near radius_small) data := by
    exact hasFDerivAt_holderContourVelocity data near radius_small
  have value : DifferentiableAt ℝ
      (fun current : PeriodicC1HolderHalf => (holderContourVelocity current).val.1) data := by
    have derivative : HasFDerivAt
        (fun current : PeriodicC1HolderHalf => (holderContourVelocity current).val.1)
        (holderValueFunctionRealCLM.comp (contourVelocityHolderDerivativeCLM data near radius_small)) data := by
      exact holderValueFunctionRealCLM.hasFDerivAt.comp data value_derivative
    exact HasFDerivAt.differentiableAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := ℝ →ᵇ ℂ) derivative
  have tangent : DifferentiableAt ℝ holderContourVelocityTangent data :=
    differentiableAt_holderContourVelocityTangent data small
  have pair : DifferentiableAt ℝ
      (fun current : PeriodicC1HolderHalf => ((holderContourVelocity current).val.1, holderContourVelocityTangent current)) data := by
    exact DifferentiableAt.prodMk (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := ℝ →ᵇ ℂ) (G := PeriodicHolderHalf) value tangent
  have equality : (fun current : PeriodicC1HolderHalf => (extendedContourVelocity current).val) =ᶠ[𝓝 data]
      (fun current : PeriodicC1HolderHalf => ((holderContourVelocity current).val.1, holderContourVelocityTangent current)) := by
    have positive : 0 < radius - ‖data - standardCircleBanach‖ := sub_pos.mpr near
    filter_upwards [Metric.ball_mem_nhds data positive] with current member
    have distance : ‖current - data‖ < radius - ‖data - standardCircleBanach‖ := by
      rw [mem_ball, dist_eq_norm current data] at member
      exact member
    have current_near : ‖current - standardCircleBanach‖ < radius := by
      have triangle := dist_triangle current data standardCircleBanach
      rw [dist_eq_norm current standardCircleBanach, dist_eq_norm current data,
        dist_eq_norm data standardCircleBanach] at triangle
      linarith
    exact extendedContourVelocity_ambient_eq current (current_near.trans radius_small)
  have ambient : DifferentiableAt ℝ
      (fun current : PeriodicC1HolderHalf => (extendedContourVelocity current).val) data := by
    exact DifferentiableAt.congr_of_eventuallyEq (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := C1HolderGraphAmbient) pair equality
  have derivative := hasFDerivAt_closedSubmodule periodicC1HolderGraph periodicC1HolderGraph_isClosed
    (DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := C1HolderGraphAmbient) ambient)
  exact HasFDerivAt.differentiableAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) derivative

end

end EulerNonuniqueness.Paper
