import EulerNonuniqueness.Section3.ContourSecondOperatorHolomorphic

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

attribute [local instance] secondOperatorLipHolderModule secondOperatorLipC1Module
  derivativeOperatorHolderSpace derivativeOperatorC1Space
  derivativeOperatorGroup derivativeOperatorModule derivativeOperatorSpace
  derivativeDensityOperatorGroup derivativeDensityOperatorModule derivativeDensityOperatorSpace
  secondFamilyDerivativeGroup secondFamilyDerivativeSub secondLineDerivativeAddCommGroup
  secondLineDensityContinuousAdd secondLineDerivativeModule secondLineDerivativeSpace

local instance higherCauchyOperatorSMul : SMul ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := by
  with_reducible
    exact ContinuousLinearMap.instSMul (R₁ := ℂ) (R₂ := ℂ) (S₂ := ℂ) (M₁ := PeriodicC1HolderHalf)
      (M₂ := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

local instance higherCauchyDensitySMul : SMul ℂ
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := by
  with_reducible
    exact ContinuousLinearMap.instSMul (R₁ := ℂ) (R₂ := ℂ) (S₂ := ℂ) (M₁ := PeriodicHolderHalf)
      (M₂ := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

local instance higherCauchyFamilySMul : SMul ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := by
  with_reducible
    exact ContinuousLinearMap.instSMul (R₁ := ℂ) (R₂ := ℂ) (S₂ := ℂ) (M₁ := PeriodicC1HolderHalf)
      (M₂ := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

local instance higherCauchyFamilyBoundedSMul : IsBoundedSMul ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := by
  with_reducible
    exact NormedSpace.isBoundedSMul (𝕜 := ℂ)
      (E := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)

local instance higherCauchyFamilyUniformity : UniformSpace
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  secondFamilyDerivativeGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace

local instance higherCauchyFamilyTopology : TopologicalSpace
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  higherCauchyFamilyUniformity.toTopologicalSpace

local instance higherCauchyFamilyContinuousSMul : ContinuousSMul ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := by
  with_reducible
    exact IsBoundedSMul.continuousSMul (α := ℂ)
      (β := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)

end

end EulerNonuniqueness.Paper
