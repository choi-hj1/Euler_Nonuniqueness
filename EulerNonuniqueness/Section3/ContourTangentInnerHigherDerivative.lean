import EulerNonuniqueness.Section3.ContourCauchyJointHigherDerivative
import EulerNonuniqueness.Section3.ContourQuotientHigherDerivative
import EulerNonuniqueness.Section3.ContourTangentInnerDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance innerHigherHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance innerHigherC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance innerHigherEndGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance innerHigherEndSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance innerHigherHolderComplexModule : Module ℂ PeriodicHolderHalf := Submodule.module complexPeriodicHolderGraph
local instance innerHigherOperatorComplexModule : Module ℂ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℂ) (M := PeriodicC1HolderHalf) (M₃ := PeriodicHolderHalf) (σ₁₃ := RingHom.id ℝ)
local instance innerHigherOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance innerHigherOperatorRealSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance innerHigherOperatorComplexSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

def extendedContourTangentInnerDerivativeCLM (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf :=
  (extendedContourCauchyJointDerivativeCLM data (extendedContourTangentQuotient data)).comp
      ((ContinuousLinearMap.id ℝ PeriodicC1HolderHalf).prod (contourQuotientDerivativeCLM data)) +
    ((Real.pi : ℂ) * Complex.I) • contourQuotientDerivativeCLM data

theorem extendedContourTangentInnerDerivativeCLM_eq (data : PeriodicC1HolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    extendedContourTangentInnerDerivativeCLM data = contourTangentInnerDerivativeCLM data near small := by
  unfold extendedContourTangentInnerDerivativeCLM contourTangentInnerDerivativeCLM
  rw [extendedContourCauchyJointDerivativeCLM_eq data _ near small]

theorem differentiableAt_extendedContourTangentInnerDerivativeCLM (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    DifferentiableAt ℝ extendedContourTangentInnerDerivativeCLM data := by
  have density := (analyticAt_extendedContourTangentQuotient data (near.trans (gap.trans small))).differentiableAt
  have joint := differentiableAt_extendedContourCauchyJointDerivativeCLM_comp_density data _ near gap small density
  have quotient := (analyticAt_contourQuotientDerivativeCLM data (near.trans (gap.trans small))).differentiableAt
  have identity : DifferentiableAt ℝ (fun _ : PeriodicC1HolderHalf => ContinuousLinearMap.id ℝ PeriodicC1HolderHalf) data :=
    differentiableAt_const (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (x := data) _
  have pair := EulerNonuniqueness.General.differentiableAt_clm_prod
    (D := PeriodicC1HolderHalf) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (G := PeriodicHolderHalf) identity quotient
  have composed := DifferentiableAt.clm_comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf) (G := PeriodicC1HolderHalf × PeriodicHolderHalf) (H := PeriodicHolderHalf) joint pair
  exact composed.add (quotient.const_smul ((Real.pi : ℂ) * Complex.I))

end

end EulerNonuniqueness.Paper
