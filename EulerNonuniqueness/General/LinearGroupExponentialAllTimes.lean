import EulerNonuniqueness.General.LinearGroupExponentialIdentification
import EulerNonuniqueness.General.LinearExponentialGroup

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem linearGroup_eq_exponential_all_times
    (group : ℝ → Space →L[ℝ] Space) (operator : Space →L[ℝ] Space)
    (identity : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second, group (first + second) = (group first).comp (group second))
    (derivative : ∀ time, HasDerivAt group ((group time).comp operator) time) (time : ℝ) :
    group time = linearExponentialGroup operator time := by
  by_cases nonnegative : 0 ≤ time
  · exact linearGroup_eq_exp_of_nonnegative group operator identity addition derivative nonnegative
  · have negNonnegative : 0 ≤ -time := by linarith
    have negative := linearGroup_eq_exp_of_nonnegative group operator identity addition derivative negNonnegative
    change group (-time) = linearExponentialGroup operator (-time) at negative
    have groupInverse : (group time).comp (group (-time)) = ContinuousLinearMap.id ℝ Space := by
      rw [← addition, add_neg_cancel, identity]
    have exponentialInverse : (linearExponentialGroup operator (-time)).comp
        (linearExponentialGroup operator time) = ContinuousLinearMap.id ℝ Space := by
      rw [← linearExponentialGroup_add, neg_add_cancel, linearExponentialGroup_zero]
    apply ContinuousLinearMap.ext
    intro value
    have inverseValue := congrArg (fun linear : Space →L[ℝ] Space => linear value) exponentialInverse
    change linearExponentialGroup operator (-time) (linearExponentialGroup operator time value) = value at inverseValue
    rw [← negative] at inverseValue
    calc
      group time value = group time (group (-time) (linearExponentialGroup operator time value)) :=
        congrArg (group time) inverseValue.symm
      _ = linearExponentialGroup operator time value :=
        congrArg (fun linear : Space →L[ℝ] Space => linear (linearExponentialGroup operator time value)) groupInverse

end

end EulerNonuniqueness.General
