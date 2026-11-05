import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Parameter Space : Type*}
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem differentiate_operator_intertwining
    (operator coordinates : Parameter → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (base : Parameter) (operatorDerivative coordinateDerivative : Parameter →L[ℝ] Space →L[ℝ] Space)
    (operatorActual : HasFDerivAt operator operatorDerivative base)
    (coordinatesActual : HasFDerivAt coordinates coordinateDerivative base)
    (intertwines : ∀ᶠ point in 𝓝 base,
      (operator point).comp (coordinates point) = (coordinates point).comp generator)
    (parameterDirection : Parameter) (direction : Space) :
    operatorDerivative parameterDirection (coordinates base direction) +
        operator base (coordinateDerivative parameterDirection direction) =
      coordinateDerivative parameterDirection (generator direction) := by
  have leftDerivative := operatorActual.clm_comp coordinatesActual
  have constantDerivative : HasFDerivAt (fun _ : Parameter => generator)
      (0 : Parameter →L[ℝ] Space →L[ℝ] Space) base := hasFDerivAt_const generator base
  have rightDerivative := coordinatesActual.clm_comp constantDerivative
  have equalityNear : (fun point => (operator point).comp (coordinates point)) =ᶠ[𝓝 base]
      (fun point => (coordinates point).comp generator) := intertwines
  have leftAsRight := leftDerivative.congr_of_eventuallyEq equalityNear.symm
  have equality := leftAsRight.unique rightDerivative
  have applied := congrArg
    (fun derivative : Parameter →L[ℝ] Space →L[ℝ] Space => derivative parameterDirection direction) equality
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add] at applied
  simpa only [add_comm] using applied

end EulerNonuniqueness.General
