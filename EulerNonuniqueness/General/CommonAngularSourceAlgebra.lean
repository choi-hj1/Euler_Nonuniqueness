import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem commonAngularSource_identity
    (parameterDerivative angularProjection inverseDerivative correction : Space →L[ℝ] Space)
    (self firstForce finalForce : Space) :
    parameterDerivative (angularProjection (inverseDerivative (self + finalForce))) +
        (ContinuousLinearMap.id ℝ Space - correction) (finalForce - firstForce) =
      parameterDerivative (angularProjection (inverseDerivative (self + firstForce))) +
        (ContinuousLinearMap.id ℝ Space - correction +
          parameterDerivative.comp (angularProjection.comp inverseDerivative)) (finalForce - firstForce) := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_add, map_sub]
  abel

end EulerNonuniqueness.General
