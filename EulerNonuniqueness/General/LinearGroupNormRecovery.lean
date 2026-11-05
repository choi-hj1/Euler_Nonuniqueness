import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem linear_group_scaled_apply_neg
    (group : ℝ → Space →L[ℝ] Space)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second, group (first + second) = (group first).comp (group second))
    (frequency time : ℝ) (data : Space) :
    group (frequency * time) (group (frequency * (-time)) data) = data := by
  have actual := congrArg (fun operator : Space →L[ℝ] Space => operator data)
    (addition (frequency * time) (frequency * (-time)))
  rw [show frequency * time + frequency * (-time) = 0 by ring, atZero] at actual
  exact actual.symm

theorem linear_group_scaled_norm_recovery
    (group : ℝ → Space →L[ℝ] Space)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second, group (first + second) = (group first).comp (group second))
    (constant : ℝ) (bound : ∀ time data, ‖group time data‖ ≤ constant * ‖data‖)
    (frequency time : ℝ) (data : Space) :
    ‖data‖ ≤ constant * ‖group (frequency * (-time)) data‖ := by
  have actual := bound (frequency * time) (group (frequency * (-time)) data)
  rwa [linear_group_scaled_apply_neg group atZero addition] at actual

end EulerNonuniqueness.General
