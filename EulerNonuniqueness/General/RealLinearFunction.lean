import Mathlib

namespace EulerNonuniqueness.General

variable {Domain Target : Type*} [AddCommMonoid Domain] [Module ℝ Domain]
  [AddCommMonoid Target] [Module ℝ Target]

def realLinearFunction (function : Domain → Target)
    (additive : ∀ first second, function (first + second) = function first + function second)
    (homogeneous : ∀ (scalar : ℝ) direction, function (scalar • direction) = scalar • function direction) :
    Domain →ₗ[ℝ] Target where
  toFun := function
  map_add' := additive
  map_smul' := homogeneous

theorem realLinearFunction_apply (function : Domain → Target)
    (additive : ∀ first second, function (first + second) = function first + function second)
    (homogeneous : ∀ (scalar : ℝ) direction, function (scalar • direction) = scalar • function direction)
    (direction : Domain) : realLinearFunction function additive homogeneous direction = function direction := rfl

end EulerNonuniqueness.General
