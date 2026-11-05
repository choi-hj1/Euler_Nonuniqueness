import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace EulerNonuniqueness.General

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open Filter
open scoped Topology

variable {Domain Value Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem derivative_hasLipschitzDerivativeNear_composition
    (function : Value → Range) (chart : Domain → Value) (base : Domain)
    (functionRegular : HasLipschitzDerivativeNear function (chart base))
    (functionSecond : HasLipschitzDerivativeNear (fderiv ℝ function) (chart base))
    (chartRegular : HasLipschitzDerivativeNear chart base)
    (chartSecond : HasLipschitzDerivativeNear (fderiv ℝ chart) base) :
    HasLipschitzDerivativeNear (fderiv ℝ (fun point => function (chart point))) base := by
  have first := functionSecond.comp chartRegular
  have expression := HasLipschitzDerivativeNear.bilinear
    (ContinuousLinearMap.compL ℝ Domain Value Range) first chartSecond
  apply expression.congr
  filter_upwards [chartRegular.1, chartRegular.lipschitzNear.continuousAt.eventually functionRegular.1]
    with point chartDerivative functionDerivative
  exact fderiv_comp point functionDerivative chartDerivative

theorem derivative_hasLipschitzDerivativeNear_operator_apply
    (coefficient : Domain → Value →L[ℝ] Range) (value : Domain → Value) (base : Domain)
    (coefficientRegular : HasLipschitzDerivativeNear coefficient base)
    (coefficientSecond : HasLipschitzDerivativeNear (fderiv ℝ coefficient) base)
    (valueRegular : HasLipschitzDerivativeNear value base)
    (valueSecond : HasLipschitzDerivativeNear (fderiv ℝ value) base) :
    HasLipschitzDerivativeNear (fderiv ℝ (fun point => coefficient point (value point))) base := by
  have firstTerm := HasLipschitzDerivativeNear.bilinear
    (ContinuousLinearMap.compL ℝ Domain Value Range) coefficientRegular valueSecond
  let flipMap : (Domain →L[ℝ] Value →L[ℝ] Range) →L[ℝ] Value →L[ℝ] Domain →L[ℝ] Range :=
    (ContinuousLinearMap.flipₗᵢ ℝ Domain Value Range).toContinuousLinearEquiv.toContinuousLinearMap
  have flipped : HasLipschitzDerivativeNear
      (fun point => (fderiv ℝ coefficient point).flip) base := by
    change HasLipschitzDerivativeNear (fun point => flipMap (fderiv ℝ coefficient point)) base
    exact HasLipschitzDerivativeNear.comp (Space := Domain)
      (Middle := Domain →L[ℝ] Value →L[ℝ] Range)
      (Target := Value →L[ℝ] Domain →L[ℝ] Range) (outer := fun operator => flipMap operator)
      (inner := fderiv ℝ coefficient)
      (hasLipschitzDerivativeNear_continuousLinearMap
        (Space := Domain →L[ℝ] Value →L[ℝ] Range)
        (Target := Value →L[ℝ] Domain →L[ℝ] Range)
        flipMap (fderiv ℝ coefficient base)) coefficientSecond
  have secondTerm := HasLipschitzDerivativeNear.bilinear
    (ContinuousLinearMap.id ℝ (Value →L[ℝ] Domain →L[ℝ] Range)) flipped valueRegular
  apply (firstTerm.add secondTerm).congr
  filter_upwards [coefficientRegular.1, valueRegular.1] with point coefficientDerivative valueDerivative
  exact fderiv_clm_apply coefficientDerivative valueDerivative

end

end EulerNonuniqueness.General
