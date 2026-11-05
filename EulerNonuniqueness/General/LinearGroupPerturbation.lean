import EulerNonuniqueness.General.LinearGroupDuhamel

namespace EulerNonuniqueness.General

noncomputable section

open MeasureTheory Set

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem linearGroup_perturbation_formula
    (group : ℝ → Space →L[ℝ] Space) (generator perturbed : Space →L[ℝ] Space)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (groupDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (trajectory : ℝ → Space) {horizon time : ℝ}
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (equation : ∀ current ∈ Icc 0 horizon, HasDerivAt trajectory (perturbed (trajectory current)) current)
    (inside : time ∈ Icc 0 horizon) :
    trajectory time - group time (trajectory 0) =
      ∫ current in (0 : ℝ)..time,
        group (time - current) ((perturbed - generator) (trajectory current)) := by
  have forcingContinuous : ContinuousOn (fun current => (perturbed - generator) (trajectory current))
      (Icc 0 horizon) := (perturbed - generator).continuous.comp_continuousOn trajectoryContinuous
  have forcedEquation (current : ℝ) (currentInside : current ∈ Icc 0 horizon) :
      HasDerivAt trajectory (generator (trajectory current) +
        (perturbed - generator) (trajectory current)) current := by
    convert equation current currentInside using 1
    simp only [ContinuousLinearMap.sub_apply]
    abel
  have actual := linearGroup_duhamel group generator atZero addition groupDerivative
    trajectoryContinuous forcingContinuous forcedEquation inside
  rw [actual]
  abel

end

end EulerNonuniqueness.General
