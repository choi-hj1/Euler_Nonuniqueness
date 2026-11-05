import EulerNonuniqueness.Section3.ContourSecondOperatorLine
import EulerNonuniqueness.Section3.ContourSecondVariationHolomorphic
import EulerNonuniqueness.General.ComplexOperatorCompleteness

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
  secondFamilyDensityUniformAdd secondFamilyDensityTopologicalAdd
  secondFamilyDerivativeGroup secondFamilyDerivativeSub secondLineDerivativeAddCommGroup
  secondLineDensityContinuousAdd secondLineDerivativeModule secondLineDerivativeSpace

local instance secondHolomorphicOperatorComplete : CompleteSpace
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := by
  with_reducible
    exact EulerNonuniqueness.General.completeSpace_complexOperator
      (Domain := PeriodicC1HolderHalf) (Target := PeriodicHolderHalf)

local instance secondHolomorphicDensityComplete : CompleteSpace
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := by
  with_reducible
    exact EulerNonuniqueness.General.completeSpace_complexOperator
      (Domain := PeriodicHolderHalf) (Target := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)

local instance secondHolomorphicFamilyComplete : CompleteSpace
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) := by
  with_reducible
    exact EulerNonuniqueness.General.completeSpace_complexOperator
      (Domain := PeriodicC1HolderHalf)
      (Target := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)

def contourCauchySecondOperatorEvaluation
    (label : PeriodicC1HolderHalf × PeriodicHolderHalf × PeriodicC1HolderHalf × ℝ) :
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) →L[ℂ] ℂ :=
  (((complexHolderEvaluation label.2.2.2).comp
    (ContinuousLinearMap.apply ℂ PeriodicHolderHalf label.2.2.1)).comp
      (ContinuousLinearMap.apply ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) label.2.1)).comp
        (ContinuousLinearMap.apply ℂ
          (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) label.1)

theorem analyticAt_extendedContourCauchySecondOperatorCLM_complex_line
    (data direction : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    AnalyticAt ℂ (fun parameter : ℂ =>
      extendedContourCauchySecondOperatorCLM (data + parameter • direction)) 0 := by
  obtain ⟨innerRadius, near, innerSmall⟩ := exists_between small
  obtain ⟨outerRadius, gap, outerSmall⟩ := exists_between innerSmall
  let parameterRadius := (innerRadius - ‖data - standardCircleBanach‖) /
    (2 * (‖direction‖ + 1))
  have positive : 0 < parameterRadius := div_pos (sub_pos.mpr near) (by positivity)
  have nearby (parameter : ℂ) (inside : parameter ∈ closedBall (0 : ℂ) parameterRadius) :
      ‖data + parameter • direction - standardCircleBanach‖ < innerRadius := by
    apply complexContourPerturbation_near data direction near
    have parameterBound : ‖parameter‖ ≤ parameterRadius := by
      simpa only [mem_closedBall, dist_zero_right] using inside
    apply parameterBound.trans_lt
    dsimp only [parameterRadius]
    apply div_lt_div_of_pos_left (sub_pos.mpr near) (by positivity)
    nlinarith [norm_nonneg direction]
  have separates : ∀ first second :
      PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf,
      (∀ label, contourCauchySecondOperatorEvaluation label first =
        contourCauchySecondOperatorEvaluation label second) → first = second := by
    intro first second equal
    apply ContinuousLinearMap.ext
    intro firstDirection
    apply ContinuousLinearMap.ext
    intro density
    apply ContinuousLinearMap.ext
    intro secondDirection
    apply PeriodicHolderHalf.ext_value
    intro target
    exact equal (firstDirection, density, secondDirection, target)
  apply analyticAt_of_separating_evaluations contourCauchySecondOperatorEvaluation separates
    (radius := ⟨parameterRadius, positive.le⟩) positive
  · exact extendedContourCauchySecondOperatorCLM_continuousOn_complex_line data direction
      ((norm_nonneg _).trans near.le) gap outerSmall nearby
  · intro label
    have vectorHolomorphic := contourCauchySecondVariation_differentiableOn_complex_line
      data direction label.1 label.2.2.1 label.2.1 isOpen_ball gap outerSmall
      (fun parameter inside => (nearby parameter (ball_subset_closedBall inside)).le)
    have scalarHolomorphic : DifferentiableOn ℂ (fun parameter : ℂ =>
        complexHolderEvaluation label.2.2.2
          (contourCauchySecondVariation (data + parameter • direction) label.1 label.2.2.1 label.2.1))
        (ball (0 : ℂ) parameterRadius) := by
      intro parameter inside
      exact (complexHolderEvaluation label.2.2.2).differentiableAt.comp_differentiableWithinAt
        parameter (vectorHolomorphic parameter inside)
    apply scalarHolomorphic.congr
    intro parameter inside
    change complexHolderEvaluation label.2.2.2
      (extendedContourCauchySecondOperatorCLM (data + parameter • direction) label.1 label.2.1 label.2.2.1) = _
    rw [extendedContourCauchySecondOperatorCLM_apply _ _ _ _
      (nearby parameter (ball_subset_closedBall inside)) gap outerSmall]

end

end EulerNonuniqueness.Paper
