import EulerNonuniqueness.General.LinearExponentialConjugacy
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem equilibrium_chart_hasFDerivAt
    (field chart : Space → Space) (inverseDerivative : Space → Space →L[ℝ] Space)
    (base : Space) (linear chartLinear : Space →L[ℝ] Space)
    (inverseLinear : Space →L[ℝ] Space →L[ℝ] Space)
    (fieldDerivative : HasFDerivAt field linear (chart base))
    (chartDerivative : HasFDerivAt chart chartLinear base)
    (inverseDerivativeActual : HasFDerivAt inverseDerivative inverseLinear base)
    (equilibrium : field (chart base) = 0) :
    HasFDerivAt (fun value => inverseDerivative value (field (chart value)))
      ((inverseDerivative base).comp (linear.comp chartLinear)) base := by
  have composed := fieldDerivative.comp base chartDerivative
  have actual := inverseDerivativeActual.clm_apply composed
  simpa only [Function.comp_apply, equilibrium, map_zero, add_zero] using actual

theorem equilibrium_chart_derivative_intertwines
    (field chart : Space → Space) (inverseDerivative : Space → Space →L[ℝ] Space)
    (base : Space) (linear : Space →L[ℝ] Space) (coordinates : Space ≃L[ℝ] Space)
    (inverseLinear : Space →L[ℝ] Space →L[ℝ] Space)
    (fieldDerivative : HasFDerivAt field linear (chart base))
    (chartDerivative : HasFDerivAt chart coordinates.toContinuousLinearMap base)
    (inverseDerivativeActual : HasFDerivAt inverseDerivative inverseLinear base)
    (inverseIdentity : inverseDerivative base = coordinates.symm.toContinuousLinearMap)
    (equilibrium : field (chart base) = 0) :
    linear.comp coordinates.toContinuousLinearMap = coordinates.toContinuousLinearMap.comp
      (fderiv ℝ (fun value => inverseDerivative value (field (chart value))) base) := by
  have actual := (equilibrium_chart_hasFDerivAt field chart inverseDerivative base linear
    coordinates.toContinuousLinearMap inverseLinear fieldDerivative chartDerivative
    inverseDerivativeActual equilibrium).fderiv
  rw [actual, inverseIdentity]
  apply ContinuousLinearMap.ext
  intro direction
  exact (coordinates.apply_symm_apply (linear (coordinates direction))).symm

end

end EulerNonuniqueness.General
