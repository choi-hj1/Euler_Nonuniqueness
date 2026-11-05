import EulerNonuniqueness.Section3.ContourCauchyDerivativeOperatorFrechet
import EulerNonuniqueness.Section3.ComplexOperatorRestriction

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance realCauchyFamilyHolderReal : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance realCauchyFamilyC1Real : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance realCauchyFamilyHolderComplex : NormedSpace ℂ PeriodicHolderHalf := Submodule.normedSpace complexPeriodicHolderGraph
local instance realCauchyFamilyC1Complex : NormedSpace ℂ PeriodicC1HolderHalf := Submodule.normedSpace complexPeriodicC1HolderGraph
local instance realCauchyFamilyComplexValueGroup : NormedAddCommGroup (PeriodicHolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance realCauchyFamilyComplexValueModule : Module ℝ (PeriodicHolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℝ) (M := PeriodicHolderHalf) (M₃ := PeriodicHolderHalf) (σ₁₃ := RingHom.id ℂ)
local instance realCauchyFamilyComplexValueComplexModule : Module ℂ (PeriodicHolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℂ) (M := PeriodicHolderHalf) (M₃ := PeriodicHolderHalf) (σ₁₃ := RingHom.id ℂ)
local instance realCauchyFamilyComplexValueComplexSpace : NormedSpace ℂ (PeriodicHolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance realCauchyFamilyComplexValueRealSpace : NormedSpace ℝ (PeriodicHolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℝ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance realCauchyFamilyComplexDerivativeGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance realCauchyFamilyComplexDerivativeModule : Module ℝ (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℝ) (M := PeriodicC1HolderHalf) (M₃ := PeriodicHolderHalf) (σ₁₃ := RingHom.id ℂ)
local instance realCauchyFamilyComplexDerivativeComplexModule : Module ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℂ) (M := PeriodicC1HolderHalf) (M₃ := PeriodicHolderHalf) (σ₁₃ := RingHom.id ℂ)
local instance realCauchyFamilyComplexDerivativeRealSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance realCauchyFamilyComplexDerivativeComplexSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance realCauchyFamilyComplexDensityGroup : NormedAddCommGroup
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance realCauchyFamilyComplexDensityModule : Module ℝ
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℝ) (M := PeriodicHolderHalf)
    (M₃ := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₃ := RingHom.id ℂ)
local instance realCauchyFamilyComplexDensityComplexModule : Module ℂ
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℂ) (M := PeriodicHolderHalf)
    (M₃ := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₃ := RingHom.id ℂ)
local instance realCauchyFamilyComplexDensityComplexSpace : NormedSpace ℂ
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance realCauchyFamilyComplexDensityRealSpace : NormedSpace ℝ
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℝ) (E := PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance realCauchyFamilyComplexDensityTower : IsScalarTower ℝ ℂ
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) where
  smul_assoc first second operator := by
    apply ContinuousLinearMap.ext
    intro density
    apply ContinuousLinearMap.ext
    intro direction
    exact smul_assoc first second (operator density direction)
local instance realCauchyFamilyRealValueGroup : NormedAddCommGroup (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance realCauchyFamilyRealValueSpace : NormedSpace ℝ (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance realCauchyFamilyRealDerivativeGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance realCauchyFamilyRealDerivativeModule : Module ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℝ) (M := PeriodicC1HolderHalf) (M₃ := PeriodicHolderHalf) (σ₁₃ := RingHom.id ℝ)
local instance realCauchyFamilyRealDerivativeSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance realCauchyFamilyRealDensityGroup : NormedAddCommGroup
    (PeriodicHolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance realCauchyFamilyRealDensityModule : Module ℝ
    (PeriodicHolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℝ) (M := PeriodicHolderHalf)
    (M₃ := PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) (σ₁₃ := RingHom.id ℝ)
local instance realCauchyFamilyRealDensitySpace : NormedSpace ℝ
    (PeriodicHolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

def realContourCauchyOperatorCLM (data : PeriodicC1HolderHalf) : PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf :=
  (extendedContourCauchyOperatorCLM data).restrictScalars ℝ

def realContourCauchyDerivativeDensityCLM (data : PeriodicC1HolderHalf) :
    PeriodicHolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf :=
  ContinuousLinearMap.bilinearRestrictScalars (𝕜' := ℂ)
    (E := PeriodicHolderHalf) (F := PeriodicC1HolderHalf) (G := PeriodicHolderHalf) ℝ
    (extendedContourCauchyDerivativeDensityCLM data)

theorem differentiableAt_realContourCauchyOperatorCLM (data : PeriodicC1HolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    DifferentiableAt ℝ realContourCauchyOperatorCLM data := by
  apply EulerNonuniqueness.General.differentiableAt_restrictScalars_family
    (D := PeriodicC1HolderHalf) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf)
  exact (hasFDerivAt_extendedContourCauchyOperatorCLM data near small).differentiableAt.restrictScalars ℝ

set_option maxHeartbeats 4000000 in
theorem differentiableAt_realContourCauchyDerivativeDensityCLM (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    DifferentiableAt ℝ realContourCauchyDerivativeDensityCLM data := by
  apply EulerNonuniqueness.General.differentiableAt_bilinearRestrictScalars_family
    (D := PeriodicC1HolderHalf) (E := PeriodicHolderHalf) (F := PeriodicC1HolderHalf) (G := PeriodicHolderHalf)
  have complexDerivative : DifferentiableAt ℂ extendedContourCauchyDerivativeDensityCLM data :=
    differentiableAt_extendedContourCauchyDerivativeDensityCLM data near gap small
  exact DifferentiableAt.restrictScalars (𝕜' := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) ℝ complexDerivative

theorem realContourCauchyOperatorCLM_apply (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf) :
    realContourCauchyOperatorCLM data density = extendedContourCauchy data density :=
  extendedContourCauchyOperatorCLM_apply data density

theorem realContourCauchyDerivativeDensityCLM_apply (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    realContourCauchyDerivativeDensityCLM data density direction =
      contourCauchyDirectionalDerivative data direction density := by
  change extendedContourCauchyDerivativeDensityCLM data density direction = _
  rw [extendedContourCauchyDerivativeDensityCLM_apply data density (near.trans small),
    HasFDerivAt.fderiv (𝕜 := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
      (hasFDerivAt_extendedContourCauchy data density near small)]
  rfl

end

end EulerNonuniqueness.Paper
