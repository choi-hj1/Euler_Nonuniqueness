import EulerNonuniqueness.Section3.ContourSecondVariationOperatorLipschitz
import EulerNonuniqueness.Section3.ContourCauchyDerivativeOperatorFrechet
import EulerNonuniqueness.Section3.ComplexTrilinearUnitBound

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

attribute [local instance] secondOperatorLipHolderModule secondOperatorLipC1Module
  derivativeOperatorHolderSpace derivativeOperatorC1Space
  derivativeOperatorGroup derivativeOperatorModule derivativeOperatorSpace
  derivativeDensityOperatorGroup derivativeDensityOperatorModule derivativeDensityOperatorSpace

local instance secondFamilyDensityUniformAdd : IsUniformAddGroup
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  SeminormedAddCommGroup.to_isUniformAddGroup
    (E := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
local instance secondFamilyDensityTopologicalAdd : IsTopologicalAddGroup
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  IsUniformAddGroup.to_topologicalAddGroup
local instance secondFamilyDerivativeGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance secondFamilyDerivativeSub : Sub
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.sub (R := ℂ) (R₂ := ℂ) (M := PeriodicC1HolderHalf)
    (M₂ := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

theorem contourCauchyDerivativeDensitySecondCLM_difference_bound
    (initial final : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (initialNear : ‖initial - standardCircleBanach‖ < innerRadius)
    (finalNear : ‖final - standardCircleBanach‖ < innerRadius) :
    ‖Sub.sub (α := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (contourCauchyDerivativeDensitySecondCLM initial initialNear gap small)
      (contourCauchyDerivativeDensitySecondCLM final finalNear gap small)‖ ≤
      (16 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - innerRadius) ^ 2) *
        ‖initial - final‖ := by
  have parameterNonnegative := contourCauchyParameterOperatorConstant_nonneg (nonnegative.trans gap.le) small
  have boundNonnegative : 0 ≤
      (16 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - innerRadius) ^ 2) *
        ‖initial - final‖ := by positivity
  apply EulerNonuniqueness.General.complex_trilinear_norm_le_of_unit_norm
    (First := PeriodicC1HolderHalf) (Second := PeriodicHolderHalf)
    (Third := PeriodicC1HolderHalf) (Target := PeriodicHolderHalf) _ boundNonnegative
  intro first firstNorm
  intro density densityNorm
  intro second secondNorm
  change ‖contourCauchyDerivativeDensitySecondCLM initial initialNear gap small first density second -
    contourCauchyDerivativeDensitySecondCLM final finalNear gap small first density second‖ ≤ _
  rw [secondVariationDensity_flip_apply, secondVariationDensity_flip_apply]
  have estimate := contourCauchySecondVariation_local_difference_bound initial final first second density
    nonnegative gap small initialNear.le finalNear.le
  rw [firstNorm, secondNorm, densityNorm, mul_one] at estimate
  exact estimate.trans_eq (by ring)

theorem fderiv_extendedContourCauchyDerivativeDensityCLM_difference_bound
    (initial final : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (initialNear : ‖initial - standardCircleBanach‖ < innerRadius)
    (finalNear : ‖final - standardCircleBanach‖ < innerRadius) :
    ‖Sub.sub (α := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (fderiv ℂ extendedContourCauchyDerivativeDensityCLM initial)
      (fderiv ℂ extendedContourCauchyDerivativeDensityCLM final)‖ ≤
      (16 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - innerRadius) ^ 2) *
        ‖initial - final‖ := by
  rw [HasFDerivAt.fderiv (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
      (F := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (hasFDerivAt_extendedContourCauchyDerivativeDensityCLM initial initialNear gap small),
    HasFDerivAt.fderiv (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
      (F := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (hasFDerivAt_extendedContourCauchyDerivativeDensityCLM final finalNear gap small)]
  exact contourCauchyDerivativeDensitySecondCLM_difference_bound initial final nonnegative gap small initialNear finalNear

end

end EulerNonuniqueness.Paper
