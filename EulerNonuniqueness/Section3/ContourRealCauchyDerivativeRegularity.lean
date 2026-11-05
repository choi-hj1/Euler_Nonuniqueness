import EulerNonuniqueness.Section3.ContourCauchyDerivativeThirdRegularity

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] realCauchyFamilyHolderReal realCauchyFamilyC1Real
  realCauchyFamilyHolderComplex realCauchyFamilyC1Complex
  realCauchyFamilyComplexDerivativeGroup realCauchyFamilyComplexDerivativeModule
  realCauchyFamilyComplexDerivativeComplexModule realCauchyFamilyComplexDerivativeRealSpace
  realCauchyFamilyComplexDerivativeComplexSpace
  realCauchyFamilyComplexDensityGroup realCauchyFamilyComplexDensityModule
  realCauchyFamilyComplexDensityComplexModule realCauchyFamilyComplexDensityComplexSpace
  realCauchyFamilyComplexDensityRealSpace realCauchyFamilyComplexDensityTower
  realCauchyFamilyRealDerivativeGroup realCauchyFamilyRealDerivativeModule realCauchyFamilyRealDerivativeSpace
  thirdDensitySourceComplexModule thirdDensitySourceComplexSMul
  thirdDensitySourceBoundedSMul thirdDensitySourceContinuousSMul

local instance thirdRealDensityOperatorGroup : NormedAddCommGroup
    (PeriodicHolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance thirdRealDensityOperatorAddCommMonoid : AddCommMonoid
    (PeriodicHolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  thirdRealDensityOperatorGroup.toAddCommGroup.toAddCommMonoid
local instance thirdRealDensityOperatorSpace : NormedSpace ℝ
    (PeriodicHolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance thirdRealDensityOperatorModule : Module ℝ
    (PeriodicHolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  thirdRealDensityOperatorSpace.toModule

theorem realContourCauchyDerivativeDensity_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      realContourCauchyDerivativeDensityCLM standardCircleBanach := by
  let restriction := EulerNonuniqueness.General.complexBilinearRestrictionCLM
    (First := PeriodicHolderHalf) (Second := PeriodicC1HolderHalf) (Range := PeriodicHolderHalf)
  have outerRegular := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_continuousLinearMap
    restriction (extendedContourCauchyDerivativeDensityCLM standardCircleBanach)
  have expression := EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear.comp
    (outer := fun operator => restriction operator)
    (inner := extendedContourCauchyDerivativeDensityCLM) (point := standardCircleBanach)
    outerRegular contourCauchyDerivativeDensity_hasLipschitzSecondDerivativeNear
  apply expression.congr
  filter_upwards [] with data
  have identity := EulerNonuniqueness.General.complexBilinearRestrictionCLM_apply
    (First := PeriodicHolderHalf) (Second := PeriodicC1HolderHalf) (Range := PeriodicHolderHalf)
    (extendedContourCauchyDerivativeDensityCLM data)
  dsimp only [realContourCauchyDerivativeDensityCLM, restriction]
  with_reducible_and_instances exact identity.symm

end

end EulerNonuniqueness.Paper
