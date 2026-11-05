import EulerNonuniqueness.Section3.ContourVelocityValueHigherDerivative
import EulerNonuniqueness.Section3.ContourVelocityTangentHigherDerivative
import EulerNonuniqueness.Section3.ContourVelocityAmbientDerivative

open Filter Metric
open scoped Topology BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance ambientHigherHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance ambientHigherC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance ambientHigherHolderOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance ambientHigherHolderOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance ambientHigherValueOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] (ℝ →ᵇ ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := ℝ →ᵇ ℂ) (σ₁₂ := RingHom.id ℝ)
local instance ambientHigherValueOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] (ℝ →ᵇ ℂ)) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := ℝ →ᵇ ℂ) (σ₁₂ := RingHom.id ℝ)
local instance ambientHigherOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] C1HolderGraphAmbient) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := C1HolderGraphAmbient) (σ₁₂ := RingHom.id ℝ)
local instance ambientHigherOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] C1HolderGraphAmbient) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := C1HolderGraphAmbient) (σ₁₂ := RingHom.id ℝ)

def extendedContourVelocityAmbientDerivativeCLM (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] C1HolderGraphAmbient :=
  (holderValueFunctionRealCLM.comp (extendedContourVelocityHolderDerivativeCLM data)).prod
    (extendedContourVelocityTangentDerivativeCLM data)

theorem extendedContourVelocityAmbientDerivativeCLM_eq (data : PeriodicC1HolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    extendedContourVelocityAmbientDerivativeCLM data = contourVelocityAmbientDerivativeCLM data near small := by
  unfold extendedContourVelocityAmbientDerivativeCLM contourVelocityAmbientDerivativeCLM
  rw [extendedContourVelocityHolderDerivativeCLM_eq data near small,
    extendedContourVelocityTangentDerivativeCLM_eq data near small]

theorem differentiableAt_extendedContourVelocityAmbientDerivativeCLM (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    DifferentiableAt ℝ extendedContourVelocityAmbientDerivativeCLM data := by
  have value := EulerNonuniqueness.General.differentiableAt_const_clm_comp
    (D := PeriodicC1HolderHalf) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (G := ℝ →ᵇ ℂ) holderValueFunctionRealCLM
    (differentiableAt_extendedContourVelocityHolderDerivativeCLM data near gap small)
  exact EulerNonuniqueness.General.differentiableAt_clm_prod
    (D := PeriodicC1HolderHalf) (E := PeriodicC1HolderHalf) (F := ℝ →ᵇ ℂ) (G := PeriodicHolderHalf) value
    (differentiableAt_extendedContourVelocityTangentDerivativeCLM data near gap small)

theorem differentiableAt_fderiv_contourVelocityAmbient (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    DifferentiableAt ℝ (fun current => fderiv ℝ
      (fun argument : PeriodicC1HolderHalf => (extendedContourVelocity argument).val) current) data := by
  have equality : (fun current => fderiv ℝ
      (fun argument : PeriodicC1HolderHalf => (extendedContourVelocity argument).val) current) =ᶠ[𝓝 data]
      extendedContourVelocityAmbientDerivativeCLM := by
    have nearby : Metric.ball standardCircleBanach innerRadius ∈ 𝓝 data :=
      Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_eq_norm data standardCircleBanach] using near)
    filter_upwards [nearby] with current member
    have current_near : ‖current - standardCircleBanach‖ < innerRadius := by
      simpa only [Metric.mem_ball, dist_eq_norm current standardCircleBanach] using member
    rw [HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := C1HolderGraphAmbient)
      (hasFDerivAt_contourVelocityAmbient current current_near (gap.trans small)),
      extendedContourVelocityAmbientDerivativeCLM_eq current current_near (gap.trans small)]
  exact DifferentiableAt.congr_of_eventuallyEq (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] C1HolderGraphAmbient)
    (differentiableAt_extendedContourVelocityAmbientDerivativeCLM data near gap small) equality

end

end EulerNonuniqueness.Paper
