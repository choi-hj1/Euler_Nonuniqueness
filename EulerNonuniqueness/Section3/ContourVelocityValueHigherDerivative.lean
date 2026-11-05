import EulerNonuniqueness.Section3.ContourCauchyJointHigherDerivative
import EulerNonuniqueness.Section3.ContourVelocityHolderDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance valueHigherHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance valueHigherC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance valueHigherHolderComplexModule : Module ℂ PeriodicHolderHalf := Submodule.module complexPeriodicHolderGraph
local instance valueHigherOperatorComplexModule : Module ℂ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℂ) (M := PeriodicC1HolderHalf) (M₃ := PeriodicHolderHalf) (σ₁₃ := RingHom.id ℝ)
local instance valueHigherOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance valueHigherOperatorRealSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance valueHigherOperatorComplexSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

def extendedContourVelocityHolderDerivativeCLM (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf :=
  (Complex.I / 4) • c1ValueHolderRealCLM - (1 / (4 * Real.pi) : ℂ) •
    contourHolderConjugateRealCLM.comp
      ((extendedContourCauchyJointDerivativeCLM data (holderConjugate (c1ValueHolder data))).comp
        ((ContinuousLinearMap.id ℝ PeriodicC1HolderHalf).prod
          (contourHolderConjugateRealCLM.comp c1ValueHolderRealCLM)))

theorem extendedContourVelocityHolderDerivativeCLM_eq (data : PeriodicC1HolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    extendedContourVelocityHolderDerivativeCLM data = contourVelocityHolderDerivativeCLM data near small := by
  unfold extendedContourVelocityHolderDerivativeCLM contourVelocityHolderDerivativeCLM
  rw [extendedContourCauchyJointDerivativeCLM_eq data _ near small]

theorem differentiableAt_extendedContourVelocityHolderDerivativeCLM (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    DifferentiableAt ℝ extendedContourVelocityHolderDerivativeCLM data := by
  have density : DifferentiableAt ℝ (fun current : PeriodicC1HolderHalf =>
      holderConjugate (c1ValueHolder current)) data := by
    change DifferentiableAt ℝ (fun current => (contourHolderConjugateRealCLM.comp c1ValueHolderRealCLM) current) data
    exact ContinuousLinearMap.differentiableAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) _
  have joint := differentiableAt_extendedContourCauchyJointDerivativeCLM_comp_density data _ near gap small density
  have inner := EulerNonuniqueness.General.differentiableAt_clm_comp_const joint
    (D := PeriodicC1HolderHalf) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf × PeriodicHolderHalf) (G := PeriodicHolderHalf)
    ((ContinuousLinearMap.id ℝ PeriodicC1HolderHalf).prod
      (contourHolderConjugateRealCLM.comp c1ValueHolderRealCLM))
  have conjugate := EulerNonuniqueness.General.differentiableAt_const_clm_comp
    (D := PeriodicC1HolderHalf) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (G := PeriodicHolderHalf)
    contourHolderConjugateRealCLM inner
  have constant : DifferentiableAt ℝ (fun _ : PeriodicC1HolderHalf => (Complex.I / 4) • c1ValueHolderRealCLM) data :=
    differentiableAt_const (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) (x := data) _
  exact constant.sub (conjugate.const_smul (1 / (4 * Real.pi) : ℂ))

end

end EulerNonuniqueness.Paper
