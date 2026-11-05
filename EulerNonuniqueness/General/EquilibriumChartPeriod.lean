import EulerNonuniqueness.General.EquilibriumChartDerivative

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem equilibrium_chart_derivative_exp_period
    (field chart : Space → Space) (inverseDerivative : Space → Space →L[ℝ] Space)
    (base : Space) (linear : Space →L[ℝ] Space) (coordinates : Space ≃L[ℝ] Space)
    (inverseLinear : Space →L[ℝ] Space →L[ℝ] Space)
    (fieldDerivative : HasFDerivAt field linear (chart base))
    (chartDerivative : HasFDerivAt chart coordinates.toContinuousLinearMap base)
    (inverseDerivativeActual : HasFDerivAt inverseDerivative inverseLinear base)
    (inverseIdentity : inverseDerivative base = coordinates.symm.toContinuousLinearMap)
    (equilibrium : field (chart base) = 0) {period : ℝ}
    (originalPeriod : linearExponentialGroup linear period = ContinuousLinearMap.id ℝ Space) :
    linearExponentialGroup
      (fderiv ℝ (fun value => inverseDerivative value (field (chart value))) base) period =
      ContinuousLinearMap.id ℝ Space := by
  let charted := fderiv ℝ (fun value => inverseDerivative value (field (chart value))) base
  have intertwines := equilibrium_chart_derivative_intertwines field chart inverseDerivative base
    linear coordinates inverseLinear fieldDerivative chartDerivative inverseDerivativeActual inverseIdentity equilibrium
  have reverse : charted.comp coordinates.symm.toContinuousLinearMap =
      coordinates.symm.toContinuousLinearMap.comp linear := by
    apply ContinuousLinearMap.ext
    intro direction
    apply coordinates.injective
    have actual := congrArg (fun operator : Space →L[ℝ] Space => operator (coordinates.symm direction)) intertwines
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      coordinates.apply_symm_apply] using actual.symm
  exact linearExponentialGroup_period_of_conjugacy coordinates.symm linear charted reverse originalPeriod

end

end EulerNonuniqueness.General
