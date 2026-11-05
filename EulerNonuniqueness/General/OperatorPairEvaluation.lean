import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic

namespace EulerNonuniqueness.General

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem norm_operator_difference_apply_le (first final : Domain →L[ℝ] Range) (direction : Domain) :
    ‖first direction - final direction‖ ≤ ‖first - final‖ * ‖direction‖ :=
  (first - final).le_opNorm direction

end EulerNonuniqueness.General
