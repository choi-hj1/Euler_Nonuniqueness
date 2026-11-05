import EulerNonuniqueness.Section3.ContourThirdOperatorLipschitz

open Set Metric
open scoped NNReal

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
  thirdOperatorTargetUniformAdd thirdOperatorTargetContinuousAdd thirdOperatorGroup thirdOperatorAddCommGroup
  thirdOperatorModule thirdOperatorSpace

theorem extendedContourCauchySecondOperatorCLM_exists_derivative_lipschitz_ball :
    ∃ radius > 0, ∃ constant : ℝ≥0,
      (∀ data ∈ ball standardCircleBanach radius,
        DifferentiableAt ℂ extendedContourCauchySecondOperatorCLM data) ∧
      LipschitzOnWith constant (fderiv ℂ extendedContourCauchySecondOperatorCLM)
        (ball standardCircleBanach radius) := by
  let threshold := min 1 (2 / (3 * Real.pi))
  have thresholdPositive : 0 < threshold := by dsimp only [threshold]; positivity
  let innerRadius := threshold / 4
  let outerRadius := threshold / 2
  have innerPositive : 0 < innerRadius := by dsimp only [innerRadius]; positivity
  have gap : innerRadius < outerRadius := by dsimp only [innerRadius, outerRadius]; linarith
  have small : outerRadius < min 1 (2 / (3 * Real.pi)) := by
    change threshold / 2 < threshold
    linarith
  let constant := 256 * contourCauchyParameterOperatorConstant outerRadius /
    (outerRadius - innerRadius) ^ 3
  have constantNonnegative : 0 ≤ constant := by
    have parameterNonnegative := contourCauchyParameterOperatorConstant_nonneg (innerPositive.le.trans gap.le) small
    have gapPositive := sub_pos.mpr gap
    positivity
  refine ⟨innerRadius, innerPositive, ⟨constant, constantNonnegative⟩, ?_, ?_⟩
  · intro data member
    have near : ‖data - standardCircleBanach‖ < innerRadius := by
      with_reducible_and_instances
        simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using member
    exact (hasFDerivAt_extendedContourCauchySecondOperatorCLM data near gap small).differentiableAt
  · apply LipschitzOnWith.of_dist_le_mul
    intro initial initialInside final finalInside
    have initialNear : ‖initial - standardCircleBanach‖ < innerRadius := by
      with_reducible_and_instances
        simpa only [mem_ball, dist_eq_norm initial standardCircleBanach] using initialInside
    have finalNear : ‖final - standardCircleBanach‖ < innerRadius := by
      with_reducible_and_instances
        simpa only [mem_ball, dist_eq_norm final standardCircleBanach] using finalInside
    rw [dist_eq_norm, dist_eq_norm initial final]
    exact fderiv_extendedContourCauchySecondOperatorCLM_difference_bound initial final
      innerPositive.le gap small initialNear finalNear

end

end EulerNonuniqueness.Paper
