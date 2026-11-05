import EulerNonuniqueness.General.EquilibriumChartDerivative

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem equilibrium_chart_scalar_derivative_annihilates
    (field chart : Space → Space) (inverseDerivative : Space → Space →L[ℝ] Space)
    (scalar : Space → ℝ) (base : Space) (linear : Space →L[ℝ] Space)
    (coordinates : Space ≃L[ℝ] Space) (inverseLinear : Space →L[ℝ] Space →L[ℝ] Space)
    (fieldDerivative : HasFDerivAt field linear (chart base))
    (chartDerivative : HasFDerivAt chart coordinates.toContinuousLinearMap base)
    (inverseActual : HasFDerivAt inverseDerivative inverseLinear base)
    (inverseIdentity : inverseDerivative base = coordinates.symm.toContinuousLinearMap)
    (equilibrium : field (chart base) = 0)
    (scalarRegular : DifferentiableAt ℝ scalar (chart base))
    (annihilates : ∀ value, fderiv ℝ scalar (chart base) (linear value) = 0)
    (direction : Space) :
    fderiv ℝ (fun value => scalar (chart value)) base
      (fderiv ℝ (fun value => inverseDerivative value (field (chart value))) base direction) = 0 := by
  have scalarDerivative := scalarRegular.hasFDerivAt.comp base chartDerivative
  change HasFDerivAt (fun value => scalar (chart value))
    ((fderiv ℝ scalar (chart base)).comp coordinates.toContinuousLinearMap) base at scalarDerivative
  have intertwines := equilibrium_chart_derivative_intertwines field chart inverseDerivative base linear coordinates
    inverseLinear fieldDerivative chartDerivative inverseActual inverseIdentity equilibrium
  have pointwise := congrArg (fun operator : Space →L[ℝ] Space => operator direction) intertwines
  change linear (coordinates direction) = coordinates
    (fderiv ℝ (fun value => inverseDerivative value (field (chart value))) base direction) at pointwise
  rw [scalarDerivative.fderiv]
  change fderiv ℝ scalar (chart base)
    (coordinates (fderiv ℝ (fun value => inverseDerivative value (field (chart value))) base direction)) = 0
  rw [← pointwise]
  exact annihilates (coordinates direction)

end EulerNonuniqueness.General
