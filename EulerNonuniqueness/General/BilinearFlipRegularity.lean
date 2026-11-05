import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus

noncomputable section

namespace EulerNonuniqueness.General

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {Domain First Second Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup First] [NormedSpace ℝ First]
  [NormedAddCommGroup Second] [NormedSpace ℝ Second]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem HasLipschitzDerivativeNear.flip
    {function : Domain → First →L[ℝ] Second →L[ℝ] Target} {point : Domain}
    (regular : HasLipschitzDerivativeNear function point) :
    HasLipschitzDerivativeNear (fun current => (function current).flip) point := by
  let transformation : (First →L[ℝ] Second →L[ℝ] Target) →L[ℝ] Second →L[ℝ] First →L[ℝ] Target :=
    (ContinuousLinearMap.flipₗᵢ ℝ First Second Target).toContinuousLinearEquiv.toContinuousLinearMap
  have outer : HasLipschitzDerivativeNear
      (fun operator : First →L[ℝ] Second →L[ℝ] Target => transformation operator) (function point) := by
    with_reducible_and_instances
      exact hasLipschitzDerivativeNear_continuousLinearMap
        (Space := First →L[ℝ] Second →L[ℝ] Target)
        (Target := Second →L[ℝ] First →L[ℝ] Target) transformation (function point)
  exact HasLipschitzDerivativeNear.comp (outer := fun operator => transformation operator)
    (inner := function) outer regular

end EulerNonuniqueness.General
