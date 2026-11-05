import EulerNonuniqueness.General.LinearGroupDuhamel
import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem linearGroup_hasDerivAt_right_generator
    (group derivative : ℝ → Space →L[ℝ] Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group (derivative time) time) (time : ℝ) :
    HasDerivAt group ((group time).comp (derivative 0)) time := by
  have inner : HasDerivAt (fun current : ℝ => time + current) 1 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).const_add time
  have leftDerivative := (actualDerivative time).scomp_of_eq 0 inner (by simp)
  simp only [one_smul] at leftDerivative
  change HasDerivAt (fun current => group (time + current)) (derivative time) 0 at leftDerivative
  have functionEquality : (fun current => group (time + current)) =
      fun current => (group time).comp (group current) := funext (addition time)
  rw [functionEquality] at leftDerivative
  have rightDerivative := (ContinuousLinearMap.compL ℝ Space Space Space (group time)).hasFDerivAt.comp_hasDerivAt
    0 (actualDerivative 0)
  have derivativeEquality : derivative time = (group time).comp (derivative 0) :=
    leftDerivative.unique rightDerivative
  rw [← derivativeEquality]
  exact actualDerivative time

end EulerNonuniqueness.General
