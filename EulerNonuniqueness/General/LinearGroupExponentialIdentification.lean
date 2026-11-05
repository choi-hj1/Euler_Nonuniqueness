import EulerNonuniqueness.General.LinearExponentialCurve
import EulerNonuniqueness.General.LinearGroupPerturbation

namespace EulerNonuniqueness.General

noncomputable section

open MeasureTheory Set

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem linearGroup_eq_exp_of_nonnegative
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second, group (first + second) = (group first).comp (group second))
    (groupDerivative : ∀ time, HasDerivAt group ((group time).comp generator) time)
    {time : ℝ} (nonnegative : 0 ≤ time) : group time = NormedSpace.exp ℝ (time • generator) := by
  apply ContinuousLinearMap.ext
  intro initial
  have trajectoryContinuous : Continuous (linearExponentialCurve generator initial) :=
    continuous_iff_continuousAt.mpr (fun current => (linearExponentialCurve_analyticAt generator initial current).continuousAt)
  have actual := linearGroup_perturbation_formula group generator generator atZero addition groupDerivative
    (linearExponentialCurve generator initial) trajectoryContinuous.continuousOn
    (fun current _ => linearExponentialCurve_hasDerivAt generator initial current)
    (show time ∈ Icc (0 : ℝ) time from ⟨nonnegative, le_rfl⟩)
  simp only [linearExponentialCurve_zero, sub_self, ContinuousLinearMap.zero_apply, map_zero,
    intervalIntegral.integral_zero, sub_eq_zero] at actual
  exact actual.symm

end

end EulerNonuniqueness.General
