import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem linearGroup_scaled_hasDerivAt
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (derivative : ∀ time, HasDerivAt group ((group time).comp generator) time)
    (frequency time : ℝ) :
    HasDerivAt (fun current => group (frequency * current))
      ((group (frequency * time)).comp (frequency • generator)) time := by
  have inner : HasDerivAt (fun current : ℝ => frequency * current) frequency time := by
    simpa only [mul_one] using (hasDerivAt_id time).const_mul frequency
  have actual := (derivative (frequency * time)).scomp time inner
  convert actual using 1
  ext value
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul]

end EulerNonuniqueness.General
