import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace EulerNonuniqueness.General

open scoped Topology

variable {Space Target : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem constraint_derivative_intertwines_at_equilibrium
    {constraint : Space → Target} {field : Space → Space}
    {jacobian : Space → Space →L[ℝ] Target} {base : Space}
    {constraintDerivative : Space →L[ℝ] Target} {fieldDerivative : Space →L[ℝ] Space}
    {jacobianDerivative : Space →L[ℝ] Space →L[ℝ] Target} (targetGenerator : Target →L[ℝ] Target)
    (constraintJet : HasFDerivAt constraint constraintDerivative base)
    (fieldJet : HasFDerivAt field fieldDerivative base)
    (jacobianJet : HasFDerivAt jacobian jacobianDerivative base)
    (jacobianAt : jacobian base = constraintDerivative) (stationary : field base = 0)
    (identity : (fun point => jacobian point (field point)) =ᶠ[𝓝 base]
      fun point => targetGenerator (constraint point)) :
    constraintDerivative.comp fieldDerivative = targetGenerator.comp constraintDerivative := by
  have actual := jacobianJet.clm_apply fieldJet
  have right := targetGenerator.hasFDerivAt.comp base constraintJet
  have comparison := right.congr_of_eventuallyEq identity
  have same := actual.unique comparison
  simpa only [stationary, ContinuousLinearMap.flip_apply, map_zero, zero_add, add_zero, jacobianAt] using same

theorem constraint_projection_commutes
    (generator : Space →L[ℝ] Space) (targetGenerator : Target →L[ℝ] Target)
    (constraint : Space →L[ℝ] Target) (constant : Target →L[ℝ] Space)
    (constraintIntertwines : constraint.comp generator = targetGenerator.comp constraint)
    (constantIntertwines : generator.comp constant = constant.comp targetGenerator) :
    (ContinuousLinearMap.id ℝ Space - constant.comp constraint).comp generator =
      generator.comp (ContinuousLinearMap.id ℝ Space - constant.comp constraint) := by
  apply ContinuousLinearMap.ext
  intro value
  have first := congrArg (fun linear : Space →L[ℝ] Target => linear value) constraintIntertwines
  have second := congrArg (fun linear : Target →L[ℝ] Space => linear (constraint value)) constantIntertwines
  simp only [ContinuousLinearMap.comp_apply] at first second
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub, first, second]

end EulerNonuniqueness.General
