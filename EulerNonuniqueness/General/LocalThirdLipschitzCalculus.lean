import EulerNonuniqueness.General.LocalOperatorRegularity

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Value Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem derivative_hasLipschitzSecondDerivativeNear_composition
    (function : Value → Range) (chart : Domain → Value) (base : Domain)
    (functionRegular : HasLipschitzSecondDerivativeNear function (chart base))
    (functionThird : HasLipschitzSecondDerivativeNear (fderiv ℝ function) (chart base))
    (chartRegular : HasLipschitzSecondDerivativeNear chart base)
    (chartThird : HasLipschitzSecondDerivativeNear (fderiv ℝ chart) base) :
    HasLipschitzSecondDerivativeNear (fderiv ℝ (fun point => function (chart point))) base := by
  have first := functionThird.comp chartRegular
  have expression := HasLipschitzSecondDerivativeNear.bilinear
    (ContinuousLinearMap.compL ℝ Domain Value Range) first chartThird
  apply expression.congr
  filter_upwards [chartRegular.1.1,
    chartRegular.1.lipschitzNear.continuousAt.eventually functionRegular.1.1]
    with point chartDerivative functionDerivative
  exact fderiv_comp point functionDerivative chartDerivative

theorem derivative_hasLipschitzSecondDerivativeNear_operator_apply
    (coefficient : Domain → Value →L[ℝ] Range) (value : Domain → Value) (base : Domain)
    (coefficientRegular : HasLipschitzSecondDerivativeNear coefficient base)
    (coefficientThird : HasLipschitzSecondDerivativeNear (fderiv ℝ coefficient) base)
    (valueRegular : HasLipschitzSecondDerivativeNear value base)
    (valueThird : HasLipschitzSecondDerivativeNear (fderiv ℝ value) base) :
    HasLipschitzSecondDerivativeNear (fderiv ℝ (fun point => coefficient point (value point))) base := by
  have firstTerm := HasLipschitzSecondDerivativeNear.bilinear
    (ContinuousLinearMap.compL ℝ Domain Value Range) coefficientRegular valueThird
  let flipMap : (Domain →L[ℝ] Value →L[ℝ] Range) →L[ℝ] Value →L[ℝ] Domain →L[ℝ] Range :=
    (ContinuousLinearMap.flipₗᵢ ℝ Domain Value Range).toContinuousLinearEquiv.toContinuousLinearMap
  have flipped := HasLipschitzSecondDerivativeNear.map
    (Domain := Domain) (First := Domain →L[ℝ] Value →L[ℝ] Range)
    (Target := Value →L[ℝ] Domain →L[ℝ] Range) coefficientThird flipMap
  have secondTerm := HasLipschitzSecondDerivativeNear.bilinear
    (ContinuousLinearMap.id ℝ (Value →L[ℝ] Domain →L[ℝ] Range)) flipped valueRegular
  apply (firstTerm.add secondTerm).congr
  filter_upwards [coefficientRegular.1.1, valueRegular.1.1]
    with point coefficientDerivative valueDerivative
  exact fderiv_clm_apply coefficientDerivative valueDerivative

end

end EulerNonuniqueness.General
