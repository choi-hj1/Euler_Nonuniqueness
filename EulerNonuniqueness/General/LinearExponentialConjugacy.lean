import EulerNonuniqueness.General.LinearExponentialGroup

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem linearExponentialGroup_conjugacy
    (equivalence : Space ≃L[ℝ] Space) (original conjugate : Space →L[ℝ] Space)
    (intertwines : conjugate.comp equivalence.toContinuousLinearMap =
      equivalence.toContinuousLinearMap.comp original) (time : ℝ) :
    linearExponentialGroup conjugate time = equivalence.toContinuousLinearMap.comp
      ((linearExponentialGroup original time).comp equivalence.symm.toContinuousLinearMap) := by
  have scaled : time • conjugate = equivalence.toContinuousLinearMap *
      (time • original) * equivalence.symm.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro initial
    have equation := congrArg (fun linear : Space →L[ℝ] Space => linear (equivalence.symm initial)) intertwines
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      equivalence.apply_symm_apply] at equation
    change time • conjugate initial = equivalence (time • original (equivalence.symm initial))
    rw [equivalence.map_smul, equation]
  unfold linearExponentialGroup
  rw [scaled]
  have actual := NormedSpace.exp_units_conj ℝ equivalence.toUnit (time • original)
  convert actual using 1

theorem linearExponentialGroup_period_of_conjugacy
    (equivalence : Space ≃L[ℝ] Space) (original conjugate : Space →L[ℝ] Space)
    (intertwines : conjugate.comp equivalence.toContinuousLinearMap =
      equivalence.toContinuousLinearMap.comp original) {period : ℝ}
    (originalPeriod : linearExponentialGroup original period = ContinuousLinearMap.id ℝ Space) :
    linearExponentialGroup conjugate period = ContinuousLinearMap.id ℝ Space := by
  rw [linearExponentialGroup_conjugacy equivalence original conjugate intertwines, originalPeriod]
  apply ContinuousLinearMap.ext
  intro initial
  exact equivalence.apply_symm_apply initial

end

end EulerNonuniqueness.General
