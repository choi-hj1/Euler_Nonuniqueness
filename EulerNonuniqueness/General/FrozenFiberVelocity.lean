import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem frozen_fiber_velocity_difference
    (coordinates : Space ≃L[ℝ] Space) (derivative neutral : Space →L[ℝ] Space)
    (differential : Space →L[ℝ] Space →L[ℝ] Space) (relative velocity : Space)
    (derivativeIdentity : derivative velocity = coordinates velocity + differential (neutral velocity) relative) :
    coordinates.symm (derivative velocity) - velocity =
      coordinates.symm (differential (neutral velocity) relative) := by
  rw [derivativeIdentity, map_add, coordinates.symm_apply_apply]
  abel

theorem norm_frozen_fiber_velocity_difference_le
    (coordinates : Space ≃L[ℝ] Space) (derivative neutral : Space →L[ℝ] Space)
    (differential : Space →L[ℝ] Space →L[ℝ] Space) (relative velocity : Space)
    {inverseBound differentialBound : ℝ}
    (inverseNonnegative : 0 ≤ inverseBound) (differentialNonnegative : 0 ≤ differentialBound)
    (inverseNorm : ‖coordinates.symm.toContinuousLinearMap‖ ≤ inverseBound)
    (differentialNorm : ‖differential‖ ≤ differentialBound)
    (derivativeIdentity : derivative velocity = coordinates velocity + differential (neutral velocity) relative) :
    ‖coordinates.symm (derivative velocity) - velocity‖ ≤
      (inverseBound * differentialBound) * ‖neutral velocity‖ * ‖relative‖ := by
  rw [frozen_fiber_velocity_difference coordinates derivative neutral differential relative velocity derivativeIdentity]
  have inner : ‖differential (neutral velocity) relative‖ ≤
      differentialBound * ‖neutral velocity‖ * ‖relative‖ :=
    ((differential (neutral velocity)).le_opNorm relative).trans
      (mul_le_mul_of_nonneg_right ((differential.le_opNorm (neutral velocity)).trans
        (mul_le_mul_of_nonneg_right differentialNorm (norm_nonneg _))) (norm_nonneg _))
  calc
    _ ≤ ‖coordinates.symm.toContinuousLinearMap‖ * ‖differential (neutral velocity) relative‖ :=
      coordinates.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ inverseBound * (differentialBound * ‖neutral velocity‖ * ‖relative‖) := by gcongr
    _ = _ := by ring

end EulerNonuniqueness.General
