import EulerNonuniqueness.Section3.ContourHigherOperatorInstances
import EulerNonuniqueness.General.ComplexLineDerivative
import EulerNonuniqueness.General.AnalyticLineDerivative

open Set Metric Filter
open scoped Topology NNReal

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
  higherCauchyOperatorSMul higherCauchyDensitySMul higherCauchyFamilySMul higherCauchyFamilyBoundedSMul
  higherCauchyFamilyUniformity higherCauchyFamilyTopology higherCauchyFamilyContinuousSMul

def contourCauchyThirdDirectionalOperator (data direction : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf :=
  EulerNonuniqueness.General.complexLineDerivative extendedContourCauchySecondOperatorCLM data direction

def contourCauchyThirdDirectionalOperator_hasDerivAt
    (data direction : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :=
  EulerNonuniqueness.General.hasDerivAt_of_analyticAt
    (analyticAt_extendedContourCauchySecondOperatorCLM_complex_line data direction small)

theorem contourCauchyThirdDirectionalOperator_smul
    (data direction : PeriodicC1HolderHalf) (scalar : ℂ)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourCauchyThirdDirectionalOperator data (scalar • direction) =
      scalar • contourCauchyThirdDirectionalOperator data direction := by
  unfold contourCauchyThirdDirectionalOperator
  with_reducible
    exact EulerNonuniqueness.General.complexLineDerivative_smul
      (Domain := PeriodicC1HolderHalf)
      (Target := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      extendedContourCauchySecondOperatorCLM data direction scalar
      (analyticAt_extendedContourCauchySecondOperatorCLM_complex_line data direction small).differentiableAt

theorem contourCauchyThirdDirectionalOperator_smul_total
    (data direction : PeriodicC1HolderHalf) (scalar : ℂ) :
    contourCauchyThirdDirectionalOperator data (scalar • direction) =
      scalar • contourCauchyThirdDirectionalOperator data direction := by
  unfold contourCauchyThirdDirectionalOperator
  with_reducible
    exact EulerNonuniqueness.General.complexLineDerivative_smul_total
      (Domain := PeriodicC1HolderHalf)
      (Target := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      extendedContourCauchySecondOperatorCLM data direction scalar

def extendedContourCauchySecondOperatorCLM_differentiableAt_complex_line
    (data direction : PeriodicC1HolderHalf) (parameter : ℂ)
    (small : ‖data + parameter • direction - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :=
    EulerNonuniqueness.General.differentiableAt_complex_line_of_analyticAt_shift
      (Domain := PeriodicC1HolderHalf)
      (Target := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      extendedContourCauchySecondOperatorCLM data direction parameter
      (analyticAt_extendedContourCauchySecondOperatorCLM_complex_line
        (data + parameter • direction) direction small)

theorem extendedContourCauchySecondOperatorCLM_diffContOnCl_complex_line
    (data direction : PeriodicC1HolderHalf) {radius : ℝ≥0} (positive : 0 < radius)
    (nearby : ∀ parameter ∈ closedBall (0 : ℂ) radius,
      ‖data + parameter • direction - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    DiffContOnCl ℂ (fun parameter : ℂ =>
      extendedContourCauchySecondOperatorCLM (data + parameter • direction)) (ball (0 : ℂ) radius) := by
  constructor
  · intro parameter inside
    exact (extendedContourCauchySecondOperatorCLM_differentiableAt_complex_line data direction parameter
      (nearby parameter (ball_subset_closedBall inside))).differentiableWithinAt
  · rw [closure_ball (0 : ℂ) (show (radius : ℝ) ≠ 0 from ne_of_gt positive)]
    intro parameter inside
    exact (extendedContourCauchySecondOperatorCLM_differentiableAt_complex_line data direction parameter
      (nearby parameter inside)).continuousAt.continuousWithinAt

theorem contourCauchyThirdDirectionalOperator_norm_bound
    (data direction : PeriodicC1HolderHalf) {innerRadius outerRadius : ℝ}
    (near : ‖data - standardCircleBanach‖ < innerRadius) (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    ‖contourCauchyThirdDirectionalOperator data direction‖ ≤
      (16 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - innerRadius) ^ 2) *
        ‖direction‖ := by
  have derivative := contourCauchyThirdDirectionalOperator_hasDerivAt data direction (near.trans (gap.trans small))
  have nonnegative := contourCauchyParameterOperatorConstant_nonneg
    ((norm_nonneg _).trans (near.trans gap).le) small
  apply derivative.le_of_lip' (by positivity)
  let parameterRadius := (innerRadius - ‖data - standardCircleBanach‖) / (‖direction‖ + 1)
  have positive : 0 < parameterRadius := div_pos (sub_pos.mpr near) (by positivity)
  filter_upwards [ball_mem_nhds (0 : ℂ) positive] with parameter inside
  have perturbed := complexContourPerturbation_near data direction near
    (show ‖parameter‖ < parameterRadius by simpa only [mem_ball, dist_zero_right] using inside)
  have bound := fderiv_extendedContourCauchyDerivativeDensityCLM_difference_bound
    (data + parameter • direction) data ((norm_nonneg _).trans near.le) gap small perturbed near
  have difference : data + parameter • direction - data = parameter • direction := by abel
  have scaledNorm : ‖parameter • direction‖ = ‖parameter‖ * ‖direction‖ := by
    with_reducible exact norm_smul parameter direction
  rw [difference, scaledNorm] at bound
  have zeroBase : data + (0 : ℂ) • direction = data := by
    with_reducible simp only [zero_smul, add_zero]
  rw [zeroBase, sub_zero]
  exact bound.trans_eq (by ring)

end

end EulerNonuniqueness.Paper
