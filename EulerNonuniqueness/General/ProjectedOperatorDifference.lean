import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_projected_operator_value_le_of_base_zero
    (projection firstOperator baseOperator : Space →L[ℝ] Space) (firstValue baseValue : Space)
    {constant weight size : ℝ} (constantNonnegative : 0 ≤ constant)
    (weightNonnegative : 0 ≤ weight) (sizeNonnegative : 0 ≤ size)
    (baseZero : projection (baseOperator baseValue) = 0)
    (operatorBound : ‖firstOperator‖ ≤ constant)
    (operatorDifference : ‖firstOperator - baseOperator‖ ≤ constant * size)
    (valueBound : ‖baseValue‖ ≤ constant * weight)
    (valueDifference : ‖firstValue - baseValue‖ ≤ constant * weight * size) :
    ‖projection (firstOperator firstValue)‖ ≤
      2 * ‖projection‖ * constant ^ 2 * weight * size := by
  have identity : projection (firstOperator firstValue) =
      projection (firstOperator (firstValue - baseValue) + (firstOperator - baseOperator) baseValue) := by
    simp only [map_add, map_sub, ContinuousLinearMap.sub_apply, baseZero, sub_zero]
    abel
  rw [identity]
  calc
    _ ≤ ‖projection‖ * ‖firstOperator (firstValue - baseValue) + (firstOperator - baseOperator) baseValue‖ :=
      projection.le_opNorm _
    _ ≤ ‖projection‖ * (‖firstOperator‖ * ‖firstValue - baseValue‖ +
        ‖firstOperator - baseOperator‖ * ‖baseValue‖) := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add (firstOperator.le_opNorm _)
        ((firstOperator - baseOperator).le_opNorm _))
    _ ≤ ‖projection‖ * (constant * (constant * weight * size) +
        (constant * size) * (constant * weight)) := by gcongr
    _ = _ := by ring

end EulerNonuniqueness.General
