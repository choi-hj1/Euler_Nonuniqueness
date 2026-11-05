import EulerNonuniqueness.Section3.ContourThirdOperatorCandidate
import EulerNonuniqueness.Section3.CauchyDerivativeDifference
import EulerNonuniqueness.General.HomogeneousUnitBound

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

theorem contourCauchyThirdDirectionalOperator_unit_difference_bound
    (initial final direction : PeriodicC1HolderHalf) {innerRadius outerRadius : ℝ}
    (nonnegative : 0 ≤ innerRadius) (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (initialNear : ‖initial - standardCircleBanach‖ ≤ innerRadius)
    (finalNear : ‖final - standardCircleBanach‖ ≤ innerRadius)
    (unit : ‖direction‖ ≤ 1) :
    ‖contourCauchyThirdDirectionalOperator initial direction -
        contourCauchyThirdDirectionalOperator final direction‖ ≤
      (256 * contourCauchyParameterOperatorConstant outerRadius /
        (outerRadius - innerRadius) ^ 3) * ‖initial - final‖ := by
  let middle := (innerRadius + outerRadius) / 2
  have innerMiddle : innerRadius < middle := by dsimp only [middle]; linarith
  have middleOuter : middle < outerRadius := by dsimp only [middle]; linarith
  let radius : ℝ≥0 := ⟨(outerRadius - innerRadius) / 4, by linarith⟩
  have positive : 0 < radius := by change 0 < (outerRadius - innerRadius) / 4; linarith
  have nearby (data : PeriodicC1HolderHalf) (near : ‖data - standardCircleBanach‖ ≤ innerRadius)
      (parameter : ℂ) (inside : parameter ∈ closedBall (0 : ℂ) radius) :
      ‖data + parameter • direction - standardCircleBanach‖ < middle := by
    have parameterBound : ‖parameter‖ ≤ (outerRadius - innerRadius) / 4 := by
      simpa only [mem_closedBall, dist_zero_right] using inside
    apply (complexContourPerturbation_distance data direction parameter).trans_lt
    dsimp only [middle]
    nlinarith [norm_nonneg parameter, mul_le_mul_of_nonneg_left unit (norm_nonneg parameter)]
  have firstHolomorphic := extendedContourCauchySecondOperatorCLM_diffContOnCl_complex_line
    initial direction positive (fun parameter inside =>
      (nearby initial initialNear parameter inside).trans (middleOuter.trans small))
  have secondHolomorphic := extendedContourCauchySecondOperatorCLM_diffContOnCl_complex_line
    final direction positive (fun parameter inside =>
      (nearby final finalNear parameter inside).trans (middleOuter.trans small))
  have bounded (parameter : ℂ) (inside : parameter ∈ sphere (0 : ℂ) radius) :
      ‖extendedContourCauchySecondOperatorCLM (initial + parameter • direction) -
        extendedContourCauchySecondOperatorCLM (final + parameter • direction)‖ ≤
      (16 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - middle) ^ 2) *
        ‖initial - final‖ := by
    have estimate := fderiv_extendedContourCauchyDerivativeDensityCLM_difference_bound
      (initial + parameter • direction) (final + parameter • direction)
      (nonnegative.trans innerMiddle.le) middleOuter small
      (nearby initial initialNear parameter (sphere_subset_closedBall inside))
      (nearby final finalNear parameter (sphere_subset_closedBall inside))
    have difference : initial + parameter • direction - (final + parameter • direction) = initial - final := by abel
    rw [difference] at estimate
    exact estimate
  have estimate := cauchy_derivative_difference_bound positive firstHolomorphic secondHolomorphic bounded
  change ‖contourCauchyThirdDirectionalOperator initial direction -
      contourCauchyThirdDirectionalOperator final direction‖ ≤ _ at estimate
  apply estimate.trans_eq
  dsimp only [middle, radius, NNReal.coe_mk]
  have nonzero : outerRadius - innerRadius ≠ 0 := ne_of_gt (sub_pos.mpr gap)
  have middleDifference : outerRadius - (innerRadius + outerRadius) / 2 =
      (outerRadius - innerRadius) / 2 := by ring
  rw [middleDifference]
  field_simp [nonzero]
  ring

theorem contourCauchyThirdDirectionalOperator_difference_bound
    (initial final direction : PeriodicC1HolderHalf) {innerRadius outerRadius : ℝ}
    (nonnegative : 0 ≤ innerRadius) (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (initialNear : ‖initial - standardCircleBanach‖ ≤ innerRadius)
    (finalNear : ‖final - standardCircleBanach‖ ≤ innerRadius) :
    ‖contourCauchyThirdDirectionalOperator initial direction -
        contourCauchyThirdDirectionalOperator final direction‖ ≤
      (256 * contourCauchyParameterOperatorConstant outerRadius /
        (outerRadius - innerRadius) ^ 3) * ‖initial - final‖ * ‖direction‖ := by
  with_reducible
    exact EulerNonuniqueness.General.norm_homogeneous_sub_le_of_unit_bound
      (Domain := PeriodicC1HolderHalf)
      (Target := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (contourCauchyThirdDirectionalOperator initial)
      (contourCauchyThirdDirectionalOperator final)
      (fun scalar current => contourCauchyThirdDirectionalOperator_smul_total initial current scalar)
      (fun scalar current => contourCauchyThirdDirectionalOperator_smul_total final current scalar)
      (fun current unit => contourCauchyThirdDirectionalOperator_unit_difference_bound initial final
        current nonnegative gap small initialNear finalNear unit) direction

end

end EulerNonuniqueness.Paper
