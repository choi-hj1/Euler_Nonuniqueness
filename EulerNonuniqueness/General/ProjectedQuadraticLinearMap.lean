import EulerNonuniqueness.General.QuadraticCommutatorOperator
import EulerNonuniqueness.General.ProjectedQuadraticResonance

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def projectedQuadraticLinearMap (projection : Space →L[ℝ] Space) :
    BilinearEnd Space →L[ℝ] BilinearEnd Space :=
  (bilinearPostcomposeOperator projection).comp
    ((bilinearSecondOperator projection).comp (bilinearFirstOperator projection))

theorem projectedQuadraticLinearMap_apply (projection : Space →L[ℝ] Space)
    (bilinear : BilinearEnd Space) :
    projectedQuadraticLinearMap projection bilinear = projectedQuadratic projection bilinear := by
  ext first second
  rfl

end

end EulerNonuniqueness.General
