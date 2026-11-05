import EulerNonuniqueness.Section3.ContourVelocityAmbientHigherDerivative
import EulerNonuniqueness.Section3.ClosedSubmoduleHigherDerivative

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance velocitySecondHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance velocitySecondC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance velocitySecondEndGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance velocitySecondEndSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance velocitySecondAmbientOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] C1HolderGraphAmbient) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := C1HolderGraphAmbient) (σ₁₂ := RingHom.id ℝ)
local instance velocitySecondAmbientOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] C1HolderGraphAmbient) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := C1HolderGraphAmbient) (σ₁₂ := RingHom.id ℝ)

theorem differentiableAt_fderiv_extendedContourVelocity (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    DifferentiableAt ℝ (fun current => fderiv ℝ extendedContourVelocity current) data := by
  obtain ⟨outerRadius, outerNear, outerSmall⟩ := exists_between small
  obtain ⟨innerRadius, near, gap⟩ := exists_between outerNear
  have nearby : ∀ᶠ current in 𝓝 data, DifferentiableAt ℝ extendedContourVelocity current := by
    have ball : Metric.ball standardCircleBanach outerRadius ∈ 𝓝 data :=
      Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_eq_norm data standardCircleBanach] using outerNear)
    filter_upwards [ball] with current member
    have currentNear : ‖current - standardCircleBanach‖ < outerRadius := by
      simpa only [Metric.mem_ball, dist_eq_norm current standardCircleBanach] using member
    exact differentiableAt_extendedContourVelocity current (currentNear.trans outerSmall)
  exact differentiableAt_fderiv_closedSubmodule (domain := PeriodicC1HolderHalf) (ambient := C1HolderGraphAmbient)
    (function := extendedContourVelocity) (point := data) periodicC1HolderGraph periodicC1HolderGraph_isClosed nearby
    (differentiableAt_fderiv_contourVelocityAmbient data near gap outerSmall)

theorem continuousOn_fderiv_extendedContourVelocity :
    ContinuousOn (fun current => fderiv ℝ extendedContourVelocity current)
      (Metric.ball standardCircleBanach (min 1 (2 / (3 * Real.pi)))) := by
  intro data member
  have small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    simpa only [Metric.mem_ball, dist_eq_norm data standardCircleBanach] using member
  have actual : ContinuousAt (fun current : PeriodicC1HolderHalf => fderiv ℝ extendedContourVelocity current) data :=
    DifferentiableAt.continuousAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
      (differentiableAt_fderiv_extendedContourVelocity data small)
  exact actual.continuousWithinAt

end

end EulerNonuniqueness.Paper
