import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic

namespace EulerNonuniqueness.General

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem linear_eq_defect_of_projection_zero (linear : Space →L[ℝ] Target)
    (projected direction defect : Space) (projectionEquation : projected = direction - defect)
    (annihilation : linear projected = 0) : linear direction = linear defect := by
  have applied := congrArg linear projectionEquation
  have difference := (linear.map_sub direction defect).symm.trans (applied.symm.trans annihilation)
  exact sub_eq_zero.mp difference

end EulerNonuniqueness.General
