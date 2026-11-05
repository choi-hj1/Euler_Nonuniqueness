import Mathlib

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℂ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target]

def boundedComplexLinearMap (function : Domain → Target)
    (additive : ∀ first second, function (first + second) = function first + function second)
    (homogeneous : ∀ (scalar : ℂ) (direction : Domain), function (scalar • direction) = scalar • function direction)
    (constant : ℝ) (bounded : ∀ direction, ‖function direction‖ ≤ constant * ‖direction‖) :
    Domain →L[ℂ] Target :=
  LinearMap.mkContinuous
    { toFun := function
      map_add' := additive
      map_smul' := homogeneous }
    constant bounded

theorem boundedComplexLinearMap_apply (function : Domain → Target)
    (additive : ∀ first second, function (first + second) = function first + function second)
    (homogeneous : ∀ (scalar : ℂ) (direction : Domain), function (scalar • direction) = scalar • function direction)
    (constant : ℝ) (bounded : ∀ direction, ‖function direction‖ ≤ constant * ‖direction‖)
    (direction : Domain) : boundedComplexLinearMap function additive homogeneous constant bounded direction =
      function direction := rfl

end

end EulerNonuniqueness.General
