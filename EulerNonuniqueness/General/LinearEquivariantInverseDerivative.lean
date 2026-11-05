import EulerNonuniqueness.General.LinearConjugateJet

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem ring_inverse_intertwining (relabel : Space ≃L[ℝ] Space)
    (first second : Space →L[ℝ] Space)
    (intertwining : first.comp relabel.toContinuousLinearMap = relabel.toContinuousLinearMap.comp second)
    (value : Space) :
    Ring.inverse first (relabel value) = relabel (Ring.inverse second value) := by
  have inverseIdentity := congrArg ContinuousLinearMap.inverse intertwining
  simp only [ContinuousLinearMap.inverse_comp_equiv, ContinuousLinearMap.inverse_equiv_comp] at inverseIdentity
  have action := congrArg (fun operator : Space →L[ℝ] Space => relabel (operator (relabel value))) inverseIdentity
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearMap.ringInverse_eq_inverse] using action

theorem fderiv_linear_equivariant_global (function : Space → Space) (relabel : Space ≃L[ℝ] Space)
    (equivariant : ∀ point, function (relabel point) = relabel (function point)) (base : Space) :
    (fderiv ℝ function (relabel base)).comp relabel.toContinuousLinearMap =
      relabel.toContinuousLinearMap.comp (fderiv ℝ function base) := by
  have inverseEquivariant : ∀ point, function (relabel.symm point) = relabel.symm (function point) := by
    intro point
    apply relabel.injective
    rw [ContinuousLinearEquiv.apply_symm_apply, ← equivariant, ContinuousLinearEquiv.apply_symm_apply]
  by_cases regular : DifferentiableAt ℝ function base
  · have imageRegular : DifferentiableAt ℝ function (relabel base) :=
      (HasFDerivAt.linear_conjugate regular.hasFDerivAt relabel (Filter.Eventually.of_forall equivariant)).differentiableAt
    exact fderiv_linear_equivariant function relabel.toContinuousLinearMap base regular imageRegular
      (Filter.Eventually.of_forall equivariant)
  · have imageNotRegular : ¬DifferentiableAt ℝ function (relabel base) := by
      intro imageRegular
      have actual := (HasFDerivAt.linear_conjugate imageRegular.hasFDerivAt relabel.symm
        (Filter.Eventually.of_forall inverseEquivariant)).differentiableAt
      exact regular (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using actual)
    rw [fderiv_zero_of_not_differentiableAt regular, fderiv_zero_of_not_differentiableAt imageNotRegular,
      ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]

end EulerNonuniqueness.General
