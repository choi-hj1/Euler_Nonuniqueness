import EulerNonuniqueness.Section3.ContourThirdRealRegularity
import EulerNonuniqueness.General.LocalSecondRegularity
import EulerNonuniqueness.General.ComplexSecondDerivativeLipschitz

open Filter Metric
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
  secondFamilyDerivativeGroup secondLineDerivativeAddCommGroup
  secondLineDerivativeModule secondLineDerivativeSpace secondLineDensityContinuousAdd
  thirdRemainderFamilySub thirdRemainderFamilySMul
  thirdFrechetFamilyAddCommMonoid thirdFrechetFamilyModule thirdFrechetFamilyAdd
  thirdCauchyFamilyRealSMul thirdCauchyFamilyRealModule thirdCauchyFamilyRealSpace thirdCauchyFamilyRealTower

local instance thirdDensitySourceComplexModule : Module ℂ PeriodicC1HolderHalf :=
  realCauchyFamilyC1Complex.toModule
local instance thirdDensitySourceComplexSMul : SMul ℂ PeriodicC1HolderHalf :=
  thirdDensitySourceComplexModule.toDistribMulAction.toMulAction.toSMul
local instance thirdDensitySourceBoundedSMul : IsBoundedSMul ℂ PeriodicC1HolderHalf := by
  with_reducible_and_instances exact NormedSpace.isBoundedSMul (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
local instance thirdDensitySourceContinuousSMul : ContinuousSMul ℂ PeriodicC1HolderHalf := by
  with_reducible_and_instances exact IsBoundedSMul.continuousSMul (α := ℂ) (β := PeriodicC1HolderHalf)

local instance thirdDensityRealDerivativeGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance thirdDensityRealDerivativeModule : Module ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℝ) (M := PeriodicC1HolderHalf)
    (M₃ := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₃ := RingHom.id ℝ)
local instance thirdDensityRealDerivativeSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem contourCauchyDerivativeDensity_eventually_differentiableAt :
    ∀ᶠ data in 𝓝 standardCircleBanach,
      DifferentiableAt ℂ extendedContourCauchyDerivativeDensityCLM data := by
  let threshold := min 1 (2 / (3 * Real.pi))
  have positive : 0 < threshold := by dsimp only [threshold]; positivity
  have innerPositive : 0 < threshold / 4 := by positivity
  have gap : threshold / 4 < threshold / 2 := by linarith
  have small : threshold / 2 < min 1 (2 / (3 * Real.pi)) := by
    change threshold / 2 < threshold
    linarith
  filter_upwards [ball_mem_nhds standardCircleBanach innerPositive] with data inside
  have near : ‖data - standardCircleBanach‖ < threshold / 4 := by
    with_reducible_and_instances
      simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using inside
  have actual := hasFDerivAt_extendedContourCauchyDerivativeDensityCLM data near gap small
  with_reducible_and_instances
    exact HasFDerivAt.differentiableAt (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
      (F := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) actual

theorem contourCauchyDerivativeDensity_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      extendedContourCauchyDerivativeDensityCLM standardCircleBanach := by
  have nearby := contourCauchyDerivativeDensity_eventually_differentiableAt
  have derivativeLip := contourCauchySecondOperator_hasLipschitzDerivativeNear.lipschitzNear
  unfold extendedContourCauchySecondOperatorCLM at derivativeLip
  with_reducible_and_instances
    exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_complex
      (Space := PeriodicC1HolderHalf)
      (Target := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      nearby derivativeLip

theorem contourCauchyDerivativeDensity_derivative_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fderiv ℝ extendedContourCauchyDerivativeDensityCLM) standardCircleBanach := by
  have secondRegular := contourCauchySecondOperator_hasLipschitzDerivativeNear
  unfold extendedContourCauchySecondOperatorCLM at secondRegular
  have firstRegular := contourCauchyDerivativeDensity_eventually_differentiableAt
  with_reducible_and_instances
    exact EulerNonuniqueness.General.derivative_hasLipschitzDerivativeNear_of_complex_second
      (Domain := PeriodicC1HolderHalf)
      (Target := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (function := extendedContourCauchyDerivativeDensityCLM) firstRegular secondRegular

theorem contourCauchyDerivativeDensity_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      extendedContourCauchyDerivativeDensityCLM standardCircleBanach :=
  ⟨contourCauchyDerivativeDensity_hasLipschitzDerivativeNear,
    contourCauchyDerivativeDensity_derivative_hasLipschitzDerivativeNear⟩

end

end EulerNonuniqueness.Paper
