import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus
import Mathlib.Topology.Instances.RealVectorSpace

noncomputable section

namespace EulerNonuniqueness.General

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem hasLipschitzDerivativeNear_of_sub_preserving
    (function : Domain → Target)
    (subtraction : ∀ first second, function (first - second) = function first - function second)
    (continuous : Continuous function) (point : Domain) :
    HasLipschitzDerivativeNear function point := by
  have zero : function 0 = 0 := by simpa only [sub_self] using subtraction 0 0
  let additive : Domain →+ Target := {
    toFun := function
    map_zero' := zero
    map_add' := fun first second => by
      have equality := subtraction (first + second) second
      rw [add_sub_cancel_right] at equality
      exact (eq_sub_iff_add_eq.mp equality).symm }
  let linear : Domain →L[ℝ] Target := additive.toRealLinearMap continuous
  exact hasLipschitzDerivativeNear_continuousLinearMap linear point

end EulerNonuniqueness.General
