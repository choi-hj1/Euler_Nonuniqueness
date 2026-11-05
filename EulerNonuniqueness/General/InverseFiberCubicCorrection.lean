import Mathlib

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem inverse_fiber_cubic_correction_identity
    (coordinates jacobian : Space ≃L[ℝ] Space) (correction : Space →L[ℝ] Space)
    (linear quadratic remainder : Space)
    (jacobianIdentity : jacobian.toContinuousLinearMap = coordinates.toContinuousLinearMap + correction)
    (linearCancellation : correction linear = 0) :
    jacobian.symm (coordinates linear + quadratic + remainder) - linear - coordinates.symm quadratic =
      jacobian.symm remainder - jacobian.symm (correction (coordinates.symm quadratic)) := by
  have action (value : Space) : jacobian value = coordinates value + correction value :=
    congrArg (fun operator : Space →L[ℝ] Space => operator value) jacobianIdentity
  apply jacobian.injective
  simp only [map_sub, ContinuousLinearEquiv.apply_symm_apply]
  rw [action linear, linearCancellation, add_zero, action (coordinates.symm quadratic),
    ContinuousLinearEquiv.apply_symm_apply]
  abel

theorem norm_inverse_fiber_cubic_correction_le
    (coordinates jacobian : Space ≃L[ℝ] Space) (correction : Space →L[ℝ] Space)
    (linear quadratic remainder : Space)
    (jacobianIdentity : jacobian.toContinuousLinearMap = coordinates.toContinuousLinearMap + correction)
    (linearCancellation : correction linear = 0) :
    ‖jacobian.symm (coordinates linear + quadratic + remainder) - linear - coordinates.symm quadratic‖ ≤
      ‖jacobian.symm.toContinuousLinearMap‖ * ‖remainder‖ +
        ‖jacobian.symm.toContinuousLinearMap‖ * ‖correction‖ *
          ‖coordinates.symm.toContinuousLinearMap‖ * ‖quadratic‖ := by
  rw [inverse_fiber_cubic_correction_identity coordinates jacobian correction linear quadratic remainder
    jacobianIdentity linearCancellation]
  apply (norm_sub_le _ _).trans
  apply add_le_add (jacobian.symm.toContinuousLinearMap.le_opNorm remainder)
  calc
    ‖jacobian.symm (correction (coordinates.symm quadratic))‖ ≤
        ‖jacobian.symm.toContinuousLinearMap‖ * ‖correction (coordinates.symm quadratic)‖ :=
      jacobian.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖jacobian.symm.toContinuousLinearMap‖ *
        (‖correction‖ * ‖coordinates.symm quadratic‖) :=
      mul_le_mul_of_nonneg_left (correction.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖jacobian.symm.toContinuousLinearMap‖ *
        (‖correction‖ * (‖coordinates.symm.toContinuousLinearMap‖ * ‖quadratic‖)) := by
      gcongr
      exact coordinates.symm.toContinuousLinearMap.le_opNorm _
    _ = _ := by ring

theorem norm_inverse_fiber_cubic_correction_le_of_bounds
    (coordinates jacobian : Space ≃L[ℝ] Space) (correction : Space →L[ℝ] Space)
    (linear quadratic remainder : Space) {size constant bound : ℝ}
    (sizeNonnegative : 0 ≤ size) (constantNonnegative : 0 ≤ constant) (boundNonnegative : 0 ≤ bound)
    (jacobianIdentity : jacobian.toContinuousLinearMap = coordinates.toContinuousLinearMap + correction)
    (linearCancellation : correction linear = 0)
    (inverseCoordinates : ‖coordinates.symm.toContinuousLinearMap‖ ≤ bound)
    (inverseJacobian : ‖jacobian.symm.toContinuousLinearMap‖ ≤ bound)
    (correctionBound : ‖correction‖ ≤ bound * size)
    (quadraticBound : ‖quadratic‖ ≤ bound * size ^ 2)
    (remainderBound : ‖remainder‖ ≤ constant * size ^ 3) :
    ‖jacobian.symm (coordinates linear + quadratic + remainder) - linear - coordinates.symm quadratic‖ ≤
      (bound * constant + bound ^ 4) * size ^ 3 := by
  apply (norm_inverse_fiber_cubic_correction_le coordinates jacobian correction linear quadratic remainder
    jacobianIdentity linearCancellation).trans
  calc
    _ ≤ bound * (constant * size ^ 3) + bound * (bound * size) * bound * (bound * size ^ 2) := by
      gcongr
    _ = _ := by ring

theorem norm_fiber_error_le_of_identity
    (inverseJacobian inverseCoordinates correction : Space →L[ℝ] Space)
    (error remainder quadratic : Space)
    (identity : error = inverseJacobian remainder - inverseJacobian (correction (inverseCoordinates quadratic)))
    {size remainderConstant quadraticConstant correctionConstant jacobianConstant coordinateConstant : ℝ}
    (remainderNonnegative : 0 ≤ remainderConstant) (quadraticNonnegative : 0 ≤ quadraticConstant)
    (correctionNonnegative : 0 ≤ correctionConstant) (jacobianNonnegative : 0 ≤ jacobianConstant)
    (coordinateNonnegative : 0 ≤ coordinateConstant) (sizeNonnegative : 0 ≤ size)
    (remainderBound : ‖remainder‖ ≤ remainderConstant * size ^ 3)
    (quadraticBound : ‖quadratic‖ ≤ quadraticConstant * size ^ 2)
    (correctionBound : ‖correction‖ ≤ correctionConstant * size)
    (jacobianBound : ‖inverseJacobian‖ ≤ jacobianConstant)
    (coordinateBound : ‖inverseCoordinates‖ ≤ coordinateConstant) :
    ‖error‖ ≤ (jacobianConstant * remainderConstant +
      jacobianConstant * correctionConstant * coordinateConstant * quadraticConstant) * size ^ 3 := by
  rw [identity]
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ ‖inverseJacobian‖ * ‖remainder‖ +
        ‖inverseJacobian‖ * (‖correction‖ * (‖inverseCoordinates‖ * ‖quadratic‖)) := by
      apply add_le_add (inverseJacobian.le_opNorm _)
      apply (inverseJacobian.le_opNorm _).trans
      gcongr
      apply (correction.le_opNorm _).trans
      gcongr
      exact inverseCoordinates.le_opNorm _
    _ ≤ jacobianConstant * (remainderConstant * size ^ 3) +
        jacobianConstant * ((correctionConstant * size) * (coordinateConstant * (quadraticConstant * size ^ 2))) := by
      gcongr
    _ = _ := by ring

end EulerNonuniqueness.General
