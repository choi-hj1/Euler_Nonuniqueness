import EulerNonuniqueness.Section3.ContourThirdOperatorFrechet

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondOperatorLipHolderModule secondOperatorLipC1Module
  derivativeOperatorHolderSpace derivativeOperatorC1Space
  derivativeOperatorGroup derivativeOperatorModule derivativeOperatorSpace
  derivativeDensityOperatorGroup derivativeDensityOperatorModule derivativeDensityOperatorSpace
  secondFamilyDerivativeGroup secondFamilyDerivativeSub secondLineDerivativeAddCommGroup
  secondLineDensityContinuousAdd secondLineDerivativeModule secondLineDerivativeSpace
  secondHolomorphicOperatorComplete secondHolomorphicDensityComplete secondHolomorphicFamilyComplete
  higherCauchyOperatorSMul higherCauchyDensitySMul higherCauchyFamilySMul higherCauchyFamilyBoundedSMul
  higherCauchyFamilyUniformity higherCauchyFamilyTopology higherCauchyFamilyContinuousSMul
  thirdRemainderFamilySub thirdRemainderFamilySMul
  thirdFrechetFamilyAddCommMonoid thirdFrechetFamilyModule thirdFrechetFamilyAdd

local instance thirdOperatorTargetMulAction : MulAction ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  thirdFrechetFamilyModule.toDistribMulAction.toMulAction

local instance thirdOperatorTargetSMulComm : SMulCommClass ℂ ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) where
  smul_comm first second operator := by
    calc
      first • (second • operator) = (first * second) • operator :=
        (thirdOperatorTargetMulAction.mul_smul first second operator).symm
      _ = (second * first) • operator := congrArg (fun scalar : ℂ => scalar • operator) (mul_comm first second)
      _ = second • (first • operator) := thirdOperatorTargetMulAction.mul_smul second first operator

local instance thirdOperatorTargetUniformAdd : IsUniformAddGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  SeminormedAddCommGroup.to_isUniformAddGroup
    (E := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
local instance thirdOperatorTargetTopologicalAdd : IsTopologicalAddGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := by
  with_reducible_and_instances exact IsUniformAddGroup.to_topologicalAddGroup
local instance thirdOperatorTargetContinuousAdd : ContinuousAdd
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  thirdOperatorTargetTopologicalAdd.toContinuousAdd
local instance thirdOperatorTargetContinuousConstSMul : ContinuousConstSMul ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := by
  with_reducible_and_instances
    exact ContinuousSMul.continuousConstSMul (M := ℂ)
      (X := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
local instance thirdOperatorGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ]
      PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
    (σ₁₂ := RingHom.id ℂ)
local instance thirdOperatorAddCommGroup : AddCommGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ]
      PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := thirdOperatorGroup.toAddCommGroup
local instance thirdOperatorModule : Module ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ]
      PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℂ) (M := PeriodicC1HolderHalf)
    (M₃ := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
    (σ₁₃ := RingHom.id ℂ)
local instance thirdOperatorSpace : NormedSpace ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ]
      PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
    (σ₁₂ := RingHom.id ℂ)

theorem contourCauchyThirdOperatorCLM_difference_bound
    (initial final : PeriodicC1HolderHalf) {innerRadius outerRadius : ℝ}
    (nonnegative : 0 ≤ innerRadius) (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (initialNear : ‖initial - standardCircleBanach‖ < innerRadius)
    (finalNear : ‖final - standardCircleBanach‖ < innerRadius) :
    ‖contourCauchyThirdOperatorCLM initial initialNear gap small -
        contourCauchyThirdOperatorCLM final finalNear gap small‖ ≤
      (256 * contourCauchyParameterOperatorConstant outerRadius /
        (outerRadius - innerRadius) ^ 3) * ‖initial - final‖ := by
  have parameterNonnegative := contourCauchyParameterOperatorConstant_nonneg (nonnegative.trans gap.le) small
  have gapPositive : 0 < outerRadius - innerRadius := sub_pos.mpr gap
  apply EulerNonuniqueness.General.complex_opNorm_le_of_unit_norm
    (Source := PeriodicC1HolderHalf)
    (Target := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
    _ (by positivity)
  intro direction unit
  change ‖contourCauchyThirdOperatorCLM initial initialNear gap small direction -
    contourCauchyThirdOperatorCLM final finalNear gap small direction‖ ≤ _
  rw [contourCauchyThirdOperatorCLM_apply, contourCauchyThirdOperatorCLM_apply]
  exact contourCauchyThirdDirectionalOperator_unit_difference_bound initial final direction
    nonnegative gap small initialNear.le finalNear.le unit.le

theorem fderiv_extendedContourCauchySecondOperatorCLM_difference_bound
    (initial final : PeriodicC1HolderHalf) {innerRadius outerRadius : ℝ}
    (nonnegative : 0 ≤ innerRadius) (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (initialNear : ‖initial - standardCircleBanach‖ < innerRadius)
    (finalNear : ‖final - standardCircleBanach‖ < innerRadius) :
    ‖fderiv ℂ extendedContourCauchySecondOperatorCLM initial -
        fderiv ℂ extendedContourCauchySecondOperatorCLM final‖ ≤
      (256 * contourCauchyParameterOperatorConstant outerRadius /
        (outerRadius - innerRadius) ^ 3) * ‖initial - final‖ := by
  rw [HasFDerivAt.fderiv (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (hasFDerivAt_extendedContourCauchySecondOperatorCLM initial initialNear gap small),
    HasFDerivAt.fderiv (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (hasFDerivAt_extendedContourCauchySecondOperatorCLM final finalNear gap small)]
  exact contourCauchyThirdOperatorCLM_difference_bound initial final nonnegative gap small initialNear finalNear

end

end EulerNonuniqueness.Paper
