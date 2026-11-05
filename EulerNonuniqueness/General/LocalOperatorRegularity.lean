import EulerNonuniqueness.General.LocalSecondRegularity

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain First Second Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup First] [NormedSpace ℝ First]
  [NormedAddCommGroup Second] [NormedSpace ℝ Second]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem hasLipschitzDerivativeNear_flip
    {coefficient : Domain → First →L[ℝ] Second →L[ℝ] Target} {point : Domain}
    (regular : HasLipschitzDerivativeNear coefficient point) :
    HasLipschitzDerivativeNear
      (fun current => (ContinuousLinearMap.flipₗᵢ ℝ First Second Target) (coefficient current)) point := by
  let flip := (ContinuousLinearMap.flipₗᵢ ℝ First Second Target).toContinuousLinearEquiv.toContinuousLinearMap
  have outer := hasLipschitzDerivativeNear_continuousLinearMap
    (Space := First →L[ℝ] Second →L[ℝ] Target)
    (Target := Second →L[ℝ] First →L[ℝ] Target) flip (coefficient point)
  exact HasLipschitzDerivativeNear.comp
    (outer := fun operator => flip operator) (inner := coefficient) (point := point) outer regular

theorem HasLipschitzSecondDerivativeNear.map
    {coefficient : Domain → First} {point : Domain}
    (regular : HasLipschitzSecondDerivativeNear coefficient point)
    (linear : First →L[ℝ] Target) :
    HasLipschitzSecondDerivativeNear (fun current => linear (coefficient current)) point :=
  HasLipschitzSecondDerivativeNear.comp
    (outer := fun value => linear value) (inner := coefficient) (point := point)
    (hasLipschitzSecondDerivativeNear_continuousLinearMap linear (coefficient point)) regular

end

end EulerNonuniqueness.General
