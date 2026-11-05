import EulerNonuniqueness.Section3.ContourThirdOperatorAdditivity
import EulerNonuniqueness.Section3.QuadraticFrechetCriterion
import EulerNonuniqueness.Section3.ComplexOperatorUnitBound
import EulerNonuniqueness.General.BoundedComplexLinearMap

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

local instance thirdFrechetFamilyAddCommMonoid : AddCommMonoid
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  secondLineDerivativeAddCommGroup.toAddCommMonoid

local instance thirdFrechetFamilyModule : Module ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  secondLineDerivativeSpace.toModule

local instance thirdFrechetFamilyAdd : Add
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  thirdFrechetFamilyAddCommMonoid.toAddMonoid.toAdd

def contourCauchyThirdOperatorCLM (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ]
      PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf := by
  have additive : ∀ first second : PeriodicC1HolderHalf,
      contourCauchyThirdDirectionalOperator data (first + second) =
        contourCauchyThirdDirectionalOperator data first + contourCauchyThirdDirectionalOperator data second := by
    intro first second
    have actual := contourCauchyThirdDirectionalOperator_add data first second (near.trans (gap.trans small))
    apply ContinuousLinearMap.ext
    intro direction
    apply ContinuousLinearMap.ext
    intro density
    apply ContinuousLinearMap.ext
    intro last
    apply PeriodicHolderHalf.ext_value
    intro label
    have evaluated := congrArg (fun operator : PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ]
      PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf => (operator direction density last).val.1 label) actual
    with_reducible_and_instances
      change (contourCauchyThirdDirectionalOperator data (first + second) direction density last).val.1 label =
        (contourCauchyThirdDirectionalOperator data first direction density last).val.1 label +
          (contourCauchyThirdDirectionalOperator data second direction density last).val.1 label at evaluated ⊢
    with_reducible_and_instances exact evaluated
  have homogeneous : ∀ (scalar : ℂ) (direction : PeriodicC1HolderHalf),
      contourCauchyThirdDirectionalOperator data (scalar • direction) =
        scalar • contourCauchyThirdDirectionalOperator data direction := by
    intro scalar direction
    have actual := contourCauchyThirdDirectionalOperator_smul_total data direction scalar
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro density
    apply ContinuousLinearMap.ext
    intro last
    apply PeriodicHolderHalf.ext_value
    intro label
    have evaluated := congrArg (fun operator : PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ]
      PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf => (operator first density last).val.1 label) actual
    with_reducible_and_instances
      change (contourCauchyThirdDirectionalOperator data (scalar • direction) first density last).val.1 label =
        scalar * (contourCauchyThirdDirectionalOperator data direction first density last).val.1 label at evaluated ⊢
    with_reducible_and_instances exact evaluated
  have bounded := fun direction => contourCauchyThirdDirectionalOperator_norm_bound data direction near gap small
  with_reducible_and_instances
    exact EulerNonuniqueness.General.boundedComplexLinearMap
      (Domain := PeriodicC1HolderHalf)
      (Target := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (contourCauchyThirdDirectionalOperator data) additive homogeneous
      (16 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - innerRadius) ^ 2) bounded

theorem contourCauchyThirdOperatorCLM_apply
    (data direction : PeriodicC1HolderHalf) {innerRadius outerRadius : ℝ}
    (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    contourCauchyThirdOperatorCLM data near gap small direction =
      contourCauchyThirdDirectionalOperator data direction := rfl

theorem hasFDerivAt_extendedContourCauchySecondOperatorCLM
    (data : PeriodicC1HolderHalf) {innerRadius outerRadius : ℝ}
    (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt extendedContourCauchySecondOperatorCLM
      (contourCauchyThirdOperatorCLM data near gap small) data := by
  have radiusPositive : 0 < (outerRadius - innerRadius) / 8 :=
    div_pos (sub_pos.mpr gap) (by norm_num)
  have remainder (increment : PeriodicC1HolderHalf)
      (incrementSmall : ‖increment‖ ≤ (outerRadius - innerRadius) / 8) :
      ‖extendedContourCauchySecondOperatorCLM (data + increment) -
        extendedContourCauchySecondOperatorCLM data -
        contourCauchyThirdOperatorCLM data near gap small increment‖ ≤
      (512 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - innerRadius) ^ 3) *
        ‖increment‖ ^ 2 := by
    rw [contourCauchyThirdOperatorCLM_apply]
    exact contourCauchyThirdDirectionalOperator_quadratic_remainder_bound
      data increment ((norm_nonneg _).trans near.le) gap small near.le incrementSmall
  with_reducible_and_instances
    exact EulerNonuniqueness.General.hasFDerivAt_of_quadratic_remainder
      (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (function := extendedContourCauchySecondOperatorCLM)
      (derivative := contourCauchyThirdOperatorCLM data near gap small) (point := data)
      (radius := (outerRadius - innerRadius) / 8)
      (constant := 512 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - innerRadius) ^ 3)
      radiusPositive remainder

end

end EulerNonuniqueness.Paper
