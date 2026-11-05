import EulerNonuniqueness.Section3.ContourThirdRealInstances
import EulerNonuniqueness.Section3.ComplexLocalDerivativeLipschitz

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
  thirdOperatorGroup thirdOperatorAddCommGroup thirdOperatorModule thirdOperatorSpace
  thirdCauchyFamilyRealSMul thirdCauchyFamilyRealModule thirdCauchyFamilyRealSpace thirdCauchyFamilyRealTower

theorem contourCauchySecondOperator_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      extendedContourCauchySecondOperatorCLM standardCircleBanach := by
  obtain ⟨radius, positive, constant, differentiable, lipschitz⟩ :=
    extendedContourCauchySecondOperatorCLM_exists_derivative_lipschitz_ball
  have nearby : ∀ᶠ data in 𝓝 standardCircleBanach,
      DifferentiableAt ℂ extendedContourCauchySecondOperatorCLM data := by
    filter_upwards [ball_mem_nhds standardCircleBanach positive] with data inside
    exact differentiable data inside
  have derivativeLip : EulerNonuniqueness.General.LipschitzNear
      (fderiv ℂ extendedContourCauchySecondOperatorCLM) standardCircleBanach :=
    ⟨constant, ball standardCircleBanach radius, ball_mem_nhds standardCircleBanach positive, lipschitz⟩
  with_reducible_and_instances
    exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_complex
      (Space := PeriodicC1HolderHalf)
      (Target := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      nearby derivativeLip

end

end EulerNonuniqueness.Paper
