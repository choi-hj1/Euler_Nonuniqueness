import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic

noncomputable section

namespace EulerNonuniqueness.General

variable {Scalar Domain Range : Type*} [NontriviallyNormedField Scalar]
  [NormedAddCommGroup Domain] [NormedSpace Scalar Domain]
  [NormedAddCommGroup Range] [NormedSpace Scalar Range]

theorem norm_operator_application_sub_le (first second : Domain →L[Scalar] Range) (input other : Domain) :
    ‖first input - second other‖ ≤ ‖first‖ * ‖input - other‖ + ‖first - second‖ * ‖other‖ := by
  have identity : first input - second other = first (input - other) + (first - second) other := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [identity]
  exact (norm_add_le _ _).trans (add_le_add (first.le_opNorm _) ((first - second).le_opNorm _))

end EulerNonuniqueness.General
