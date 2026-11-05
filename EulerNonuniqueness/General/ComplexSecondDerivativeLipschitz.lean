import EulerNonuniqueness.Section3.ComplexLocalDerivativeLipschitz

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℂ Domain] [NormedSpace ℝ Domain] [IsScalarTower ℝ ℂ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target] [NormedSpace ℝ Target] [IsScalarTower ℝ ℂ Target]

theorem derivative_hasLipschitzDerivativeNear_of_complex_second
    {function : Domain → Target} {point : Domain}
    (differentiable : ∀ᶠ current in 𝓝 point, DifferentiableAt ℂ function current)
    (complexSecond : HasLipschitzDerivativeNear (fderiv ℂ function) point) :
    HasLipschitzDerivativeNear (fderiv ℝ function) point := by
  let restriction := ContinuousLinearMap.restrictScalarsL ℂ Domain Target ℝ ℝ
  have outerRegular := hasLipschitzDerivativeNear_continuousLinearMap
    restriction (fderiv ℂ function point)
  have expression := HasLipschitzDerivativeNear.comp
    (outer := fun operator => restriction operator) (inner := fderiv ℂ function)
    (point := point) outerRegular complexSecond
  apply expression.congr
  filter_upwards [differentiable] with current regular
  exact (regular.hasFDerivAt.restrictScalars ℝ).fderiv

end

end EulerNonuniqueness.General
