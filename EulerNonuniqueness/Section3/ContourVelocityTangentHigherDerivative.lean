import EulerNonuniqueness.Section3.ContourTangentInnerHigherDerivative
import EulerNonuniqueness.Section3.ContourVelocityTangentFrechet

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance tangentHigherHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance tangentHigherC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance tangentHigherHolderComplexModule : Module ℂ PeriodicHolderHalf := Submodule.module complexPeriodicHolderGraph
local instance tangentHigherOperatorComplexModule : Module ℂ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℂ) (M := PeriodicC1HolderHalf) (M₃ := PeriodicHolderHalf) (σ₁₃ := RingHom.id ℝ)
local instance tangentHigherValueOperatorGroup : NormedAddCommGroup (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance tangentHigherValueOperatorSpace : NormedSpace ℝ (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance tangentHigherOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance tangentHigherOperatorRealSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance tangentHigherOperatorComplexSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

def extendedContourVelocityTangentDerivativeCLM (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf :=
  -(1 / (4 * Real.pi) : ℂ) •
    ((holderProductRealCLM (holderConjugate data.val.2)).comp
        (contourHolderConjugateRealCLM.comp (extendedContourTangentInnerDerivativeCLM data)) +
      (holderProductRealCLM.flip (holderConjugate (contourTangentInner data))).comp
        (contourHolderConjugateRealCLM.comp c1TangentHolderRealCLM))

theorem extendedContourVelocityTangentDerivativeCLM_eq (data : PeriodicC1HolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    extendedContourVelocityTangentDerivativeCLM data = contourVelocityTangentDerivativeCLM data near small := by
  unfold extendedContourVelocityTangentDerivativeCLM contourVelocityTangentDerivativeCLM
  rw [extendedContourTangentInnerDerivativeCLM_eq data near small]
  rfl

theorem differentiableAt_extendedContourVelocityTangentDerivativeCLM (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    DifferentiableAt ℝ extendedContourVelocityTangentDerivativeCLM data := by
  have tangent : DifferentiableAt ℝ (fun current : PeriodicC1HolderHalf => holderConjugate current.val.2) data := by
    have projection : DifferentiableAt ℝ (fun current : PeriodicC1HolderHalf => current.val.2) data :=
      ContinuousLinearMap.differentiableAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
        (x := data) c1TangentHolderRealCLM
    exact DifferentiableAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
      (G := PeriodicHolderHalf) data
      (ContinuousLinearMap.differentiableAt (𝕜 := ℝ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf)
        (x := data.val.2) contourHolderConjugateRealCLM) projection
  have left := (ContinuousLinearMap.differentiableAt (𝕜 := ℝ) (E := PeriodicHolderHalf)
    (F := PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) holderProductRealCLM).comp data tangent
  have inner := EulerNonuniqueness.General.differentiableAt_const_clm_comp contourHolderConjugateRealCLM
    (D := PeriodicC1HolderHalf) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (G := PeriodicHolderHalf)
    (differentiableAt_extendedContourTangentInnerDerivativeCLM data near gap small)
  have first := DifferentiableAt.clm_comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf) (G := PeriodicHolderHalf) (H := PeriodicHolderHalf) left inner
  have inner_value := HasFDerivAt.differentiableAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
    (hasFDerivAt_contourTangentInner data near (gap.trans small))
  have conjugate := (ContinuousLinearMap.differentiableAt (𝕜 := ℝ) (E := PeriodicHolderHalf)
    (F := PeriodicHolderHalf) contourHolderConjugateRealCLM).comp data inner_value
  have right := (ContinuousLinearMap.differentiableAt (𝕜 := ℝ) (E := PeriodicHolderHalf)
    (F := PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) holderProductRealCLM.flip).comp data conjugate
  have second := EulerNonuniqueness.General.differentiableAt_clm_comp_const right
    (D := PeriodicC1HolderHalf) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (G := PeriodicHolderHalf)
    (contourHolderConjugateRealCLM.comp c1TangentHolderRealCLM)
  exact (first.add second).const_smul (-(1 / (4 * Real.pi) : ℂ))

end

end EulerNonuniqueness.Paper
