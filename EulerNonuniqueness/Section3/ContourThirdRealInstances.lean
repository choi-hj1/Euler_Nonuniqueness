import EulerNonuniqueness.Section3.ContourCauchyThirdUniform
import EulerNonuniqueness.Section3.ContourCauchyRealOperatorFamilies

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

local instance thirdCauchyFamilyRealSMul : SMul ℝ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := by
  with_reducible_and_instances
    exact ContinuousLinearMap.instSMul (R₁ := ℂ) (R₂ := ℂ) (S₂ := ℝ)
      (M₁ := PeriodicC1HolderHalf)
      (M₂ := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (σ₁₂ := RingHom.id ℂ)

local instance thirdCauchyFamilyRealModule : Module ℝ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := by
  with_reducible_and_instances
    exact ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℝ)
      (M := PeriodicC1HolderHalf)
      (M₃ := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (σ₁₃ := RingHom.id ℂ)

local instance thirdCauchyFamilyRealSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := by
  with_reducible_and_instances
    exact ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℝ)
      (E := PeriodicC1HolderHalf)
      (F := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (σ₁₂ := RingHom.id ℂ)

local instance thirdCauchyFamilyRealTower : IsScalarTower ℝ ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) where
  smul_assoc realScalar complexScalar operator := by
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro density
    apply ContinuousLinearMap.ext
    intro second
    exact smul_assoc realScalar complexScalar (operator first density second)

end

end EulerNonuniqueness.Paper
