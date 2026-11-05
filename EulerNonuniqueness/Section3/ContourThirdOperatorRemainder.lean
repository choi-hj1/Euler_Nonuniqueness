import EulerNonuniqueness.Section3.ContourThirdOperatorDifference
import EulerNonuniqueness.Section3.CauchyLineDerivativeBounds
import EulerNonuniqueness.General.HomogeneousQuadraticRemainder

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

local instance thirdRemainderFamilySub : Sub
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  secondFamilyDerivativeGroup.toAddCommGroup.toAddGroup.toSubNegMonoid.toSub

local instance thirdRemainderFamilySMul : SMul ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  secondLineDerivativeSpace.toModule.toDistribMulAction.toMulAction.toSMul

theorem contourCauchyThirdDirectionalOperator_unit_ray_remainder_bound
    (data direction : PeriodicC1HolderHalf) {innerRadius outerRadius : ℝ}
    (nonnegative : 0 ≤ innerRadius) (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (near : ‖data - standardCircleBanach‖ ≤ innerRadius) (unit : ‖direction‖ = 1)
    (parameter : ℂ) (parameterSmall : ‖parameter‖ ≤ (outerRadius - innerRadius) / 8) :
    ‖extendedContourCauchySecondOperatorCLM (data + parameter • direction) -
        extendedContourCauchySecondOperatorCLM data -
        parameter • contourCauchyThirdDirectionalOperator data direction‖ ≤
      (512 * contourCauchyParameterOperatorConstant outerRadius /
        (outerRadius - innerRadius) ^ 3) * ‖parameter‖ ^ 2 := by
  let middle := (innerRadius + outerRadius) / 2
  have innerMiddle : innerRadius < middle := by dsimp only [middle]; linarith
  have middleOuter : middle < outerRadius := by dsimp only [middle]; linarith
  let radius : ℝ≥0 := ⟨(outerRadius - innerRadius) / 4, by linarith⟩
  have positive : 0 < radius := by change 0 < (outerRadius - innerRadius) / 4; linarith
  have nearby (current : ℂ) (inside : current ∈ closedBall (0 : ℂ) radius) :
      ‖data + current • direction - standardCircleBanach‖ < middle := by
    have currentBound : ‖current‖ ≤ (outerRadius - innerRadius) / 4 := by
      simpa only [mem_closedBall, dist_zero_right] using inside
    have estimate := complexContourPerturbation_distance data direction current
    rw [unit, mul_one] at estimate
    dsimp only [middle]
    linarith
  have holomorphic := extendedContourCauchySecondOperatorCLM_diffContOnCl_complex_line
    data direction positive (fun current inside => (nearby current inside).trans (middleOuter.trans small))
  have zeroBase : data + (0 : ℂ) • direction = data := by
    with_reducible simp only [zero_smul, add_zero]
  have bounded (current : ℂ) (inside : current ∈ sphere (0 : ℂ) radius) :
      ‖extendedContourCauchySecondOperatorCLM (data + current • direction) -
        extendedContourCauchySecondOperatorCLM (data + (0 : ℂ) • direction)‖ ≤
      (16 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - middle) ^ 2) * (radius : ℝ) := by
    rw [zeroBase]
    have estimate := fderiv_extendedContourCauchyDerivativeDensityCLM_difference_bound
      (data + current • direction) data (nonnegative.trans innerMiddle.le) middleOuter small
      (nearby current (sphere_subset_closedBall inside)) (near.trans_lt innerMiddle)
    have difference : data + current • direction - data = current • direction := by abel
    have scaledNorm : ‖current • direction‖ = ‖current‖ * ‖direction‖ := by
      with_reducible exact norm_smul current direction
    have currentNorm : ‖current‖ = radius := by
      simpa only [mem_sphere, dist_zero_right] using inside
    have sourceNorm : ‖data + current • direction - data‖ = (radius : ℝ) := by
      rw [difference, scaledNorm, unit, mul_one, currentNorm]
    unfold extendedContourCauchySecondOperatorCLM
    with_reducible_and_instances
      exact estimate.trans_eq (congrArg
        (fun scalar : ℝ => (16 * contourCauchyParameterOperatorConstant outerRadius /
          (outerRadius - middle) ^ 2) * scalar) sourceNorm)
  have positionSmall : 2 * ‖parameter‖ ≤ radius := by
    change 2 * ‖parameter‖ ≤ (outerRadius - innerRadius) / 4
    linarith
  have estimate := cauchy_quadratic_remainder_bound_of_increment_bound positive holomorphic bounded positionSmall
  change ‖extendedContourCauchySecondOperatorCLM (data + parameter • direction) -
      extendedContourCauchySecondOperatorCLM (data + (0 : ℂ) • direction) -
      parameter • contourCauchyThirdDirectionalOperator data direction‖ ≤ _ at estimate
  rw [zeroBase] at estimate
  apply estimate.trans_eq
  dsimp only [middle, radius, NNReal.coe_mk]
  have gapNonzero : outerRadius - innerRadius ≠ 0 := ne_of_gt (sub_pos.mpr gap)
  have middleDifference : outerRadius - (innerRadius + outerRadius) / 2 =
      (outerRadius - innerRadius) / 2 := by ring
  rw [middleDifference]
  field_simp [gapNonzero]
  ring

theorem contourCauchyThirdDirectionalOperator_quadratic_remainder_bound
    (data increment : PeriodicC1HolderHalf) {innerRadius outerRadius : ℝ}
    (nonnegative : 0 ≤ innerRadius) (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (near : ‖data - standardCircleBanach‖ ≤ innerRadius)
    (incrementSmall : ‖increment‖ ≤ (outerRadius - innerRadius) / 8) :
    ‖extendedContourCauchySecondOperatorCLM (data + increment) -
        extendedContourCauchySecondOperatorCLM data -
        contourCauchyThirdDirectionalOperator data increment‖ ≤
      (512 * contourCauchyParameterOperatorConstant outerRadius /
        (outerRadius - innerRadius) ^ 3) * ‖increment‖ ^ 2 := by
  with_reducible_and_instances
    exact EulerNonuniqueness.General.quadratic_remainder_of_unit_lines
      (Domain := PeriodicC1HolderHalf)
      (Target := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      extendedContourCauchySecondOperatorCLM (contourCauchyThirdDirectionalOperator data) data
      (fun scalar direction => contourCauchyThirdDirectionalOperator_smul_total data direction scalar)
      (fun direction unit parameter parameterSmall =>
        contourCauchyThirdDirectionalOperator_unit_ray_remainder_bound data direction nonnegative gap small
          near unit parameter parameterSmall) increment incrementSmall

end

end EulerNonuniqueness.Paper
