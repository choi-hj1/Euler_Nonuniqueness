import EulerNonuniqueness.General.LocalSecondLipschitzCalculus

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Value Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem derivative_hasLipschitzDerivativeNear_continuousLinearMap_comp
    (linear : Value →L[ℝ] Target) {function : Domain → Value} {point : Domain}
    (regular : HasLipschitzDerivativeNear function point)
    (second : HasLipschitzDerivativeNear (fderiv ℝ function) point) :
    HasLipschitzDerivativeNear (fderiv ℝ (fun current => linear (function current))) point := by
  have linearRegular := hasLipschitzDerivativeNear_continuousLinearMap linear (function point)
  have linearSecond : HasLipschitzDerivativeNear
      (fderiv ℝ (fun value : Value => linear value)) (function point) := by
    apply (hasLipschitzDerivativeNear_const linear (function point)).congr
    filter_upwards [] with value
    exact linear.hasFDerivAt.fderiv
  exact derivative_hasLipschitzDerivativeNear_composition
    (fun value : Value => linear value) function point linearRegular linearSecond regular second

theorem derivative_hasLipschitzDerivativeNear_prodMk
    {first : Domain → Value} {second : Domain → Target} {point : Domain}
    (firstRegular : HasLipschitzDerivativeNear first point)
    (firstSecond : HasLipschitzDerivativeNear (fderiv ℝ first) point)
    (secondRegular : HasLipschitzDerivativeNear second point)
    (secondSecond : HasLipschitzDerivativeNear (fderiv ℝ second) point) :
    HasLipschitzDerivativeNear (fderiv ℝ (fun current => (first current, second current))) point := by
  let product : ((Domain →L[ℝ] Value) × (Domain →L[ℝ] Target)) →L[ℝ]
      Domain →L[ℝ] Value × Target :=
    (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := Domain) (F := Value) (G := Target) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have outerRegular := hasLipschitzDerivativeNear_continuousLinearMap product
    (fderiv ℝ first point, fderiv ℝ second point)
  have pairRegular := firstSecond.prodMk secondSecond
  have expression := HasLipschitzDerivativeNear.comp
    (outer := fun pair => product pair)
    (inner := fun current : Domain => (fderiv ℝ first current, fderiv ℝ second current))
    (point := point) outerRegular pairRegular
  apply expression.congr
  filter_upwards [firstRegular.1, secondRegular.1] with current firstDerivative secondDerivative
  exact (firstDerivative.hasFDerivAt.prodMk secondDerivative.hasFDerivAt).fderiv

end

end EulerNonuniqueness.General
