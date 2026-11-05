import EulerNonuniqueness.Section3.ContourCauchyRealOperatorFamilies
import EulerNonuniqueness.Section3.OperatorFieldCalculus

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance jointHigherHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance jointHigherC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance jointHigherDerivativeGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance jointHigherDerivativeSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance jointHigherValueGroup : NormedAddCommGroup (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance jointHigherValueSpace : NormedSpace ℝ (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance jointHigherDensityGroup : NormedAddCommGroup
    (PeriodicHolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance jointHigherDensitySpace : NormedSpace ℝ
    (PeriodicHolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance jointHigherPairOperatorGroup : NormedAddCommGroup
    ((PeriodicC1HolderHalf × PeriodicHolderHalf) →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf × PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance jointHigherPairOperatorSpace : NormedSpace ℝ
    ((PeriodicC1HolderHalf × PeriodicHolderHalf) →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf × PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

def extendedContourCauchyJointDerivativeCLM (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf) :
    (PeriodicC1HolderHalf × PeriodicHolderHalf) →L[ℝ] PeriodicHolderHalf :=
  (realContourCauchyDerivativeDensityCLM data density).comp
      (ContinuousLinearMap.fst ℝ PeriodicC1HolderHalf PeriodicHolderHalf) +
    (realContourCauchyOperatorCLM data).comp
      (ContinuousLinearMap.snd ℝ PeriodicC1HolderHalf PeriodicHolderHalf)

theorem extendedContourCauchyJointDerivativeCLM_eq (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    extendedContourCauchyJointDerivativeCLM data density = contourCauchyJointDerivativeCLM data density near small := by
  apply ContinuousLinearMap.ext
  intro pair
  change realContourCauchyDerivativeDensityCLM data density pair.1 + realContourCauchyOperatorCLM data pair.2 =
    ((contourCauchyDerivativeCLM data density near small).restrictScalars ℝ) pair.1 +
      contourCauchyOperatorCLM data (near.trans small) pair.2
  rw [realContourCauchyDerivativeDensityCLM_apply data pair.1 density near small,
    realContourCauchyOperatorCLM_apply, extendedContourCauchy_eq data _ (near.trans small)]
  rfl

theorem differentiableAt_extendedContourCauchyJointDerivativeCLM_comp_density
    (data : PeriodicC1HolderHalf) (density : PeriodicC1HolderHalf → PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (density_differentiable : DifferentiableAt ℝ density data) :
    DifferentiableAt ℝ (fun current => extendedContourCauchyJointDerivativeCLM current (density current)) data := by
  have first := DifferentiableAt.clm_apply (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (G := PeriodicHolderHalf) (H := PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf)
    (differentiableAt_realContourCauchyDerivativeDensityCLM data near gap small) density_differentiable
  have first_composed := EulerNonuniqueness.General.differentiableAt_clm_comp_const
    (D := PeriodicC1HolderHalf) (E := PeriodicC1HolderHalf × PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf) (G := PeriodicHolderHalf)
    first (ContinuousLinearMap.fst ℝ PeriodicC1HolderHalf PeriodicHolderHalf)
  have second_composed := EulerNonuniqueness.General.differentiableAt_clm_comp_const
    (D := PeriodicC1HolderHalf) (E := PeriodicC1HolderHalf × PeriodicHolderHalf)
    (F := PeriodicHolderHalf) (G := PeriodicHolderHalf)
    (differentiableAt_realContourCauchyOperatorCLM data near (gap.trans small))
    (ContinuousLinearMap.snd ℝ PeriodicC1HolderHalf PeriodicHolderHalf)
  exact first_composed.add second_composed

end

end EulerNonuniqueness.Paper
