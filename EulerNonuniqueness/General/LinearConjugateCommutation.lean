import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem commute_of_linear_conjugate (relabel : Space ≃L[ℝ] Space)
    (sourceField sourceProjection targetField targetProjection : Space →L[ℝ] Space)
    (fieldIdentity : targetField.comp relabel.toContinuousLinearMap = relabel.toContinuousLinearMap.comp sourceField)
    (projectionIdentity : targetProjection.comp relabel.toContinuousLinearMap = relabel.toContinuousLinearMap.comp sourceProjection)
    (sourceCommutes : sourceProjection.comp sourceField = sourceField.comp sourceProjection) :
    targetProjection.comp targetField = targetField.comp targetProjection := by
  have fieldValue (direction : Space) : targetField (relabel direction) = relabel (sourceField direction) :=
    congrArg (fun operator : Space →L[ℝ] Space => operator direction) fieldIdentity
  have projectionValue (direction : Space) : targetProjection (relabel direction) = relabel (sourceProjection direction) :=
    congrArg (fun operator : Space →L[ℝ] Space => operator direction) projectionIdentity
  have sourceValue (direction : Space) : sourceProjection (sourceField direction) = sourceField (sourceProjection direction) :=
    congrArg (fun operator : Space →L[ℝ] Space => operator direction) sourceCommutes
  apply ContinuousLinearMap.ext
  intro direction
  change targetProjection (targetField direction) = targetField (targetProjection direction)
  calc
    _ = targetProjection (targetField (relabel (relabel.symm direction))) := by rw [relabel.apply_symm_apply]
    _ = relabel (sourceProjection (sourceField (relabel.symm direction))) := by rw [fieldValue, projectionValue]
    _ = relabel (sourceField (sourceProjection (relabel.symm direction))) := by rw [sourceValue]
    _ = targetField (targetProjection (relabel (relabel.symm direction))) := by rw [projectionValue, fieldValue]
    _ = _ := by rw [relabel.apply_symm_apply]

end EulerNonuniqueness.General
