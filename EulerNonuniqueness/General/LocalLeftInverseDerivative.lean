import Mathlib.Analysis.Calculus.FDeriv.Comp

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem derivative_of_local_left_inverse
    (forward inverse : Space → Space) (base : Space) (coordinates : Space ≃L[ℝ] Space)
    (inverseLinear : Space →L[ℝ] Space)
    (leftInverse : ∀ᶠ point in 𝓝 base, inverse (forward point) = point)
    (forwardActual : HasFDerivAt forward coordinates.toContinuousLinearMap base)
    (inverseActual : HasFDerivAt inverse inverseLinear (forward base)) :
    inverseLinear = coordinates.symm.toContinuousLinearMap := by
  have actual := inverseActual.comp base forwardActual
  have equalityNear : (fun point => inverse (forward point)) =ᶠ[𝓝 base] (fun point => point) := leftInverse
  have identityDerivative := actual.congr_of_eventuallyEq equalityNear.symm
  have linearIdentity := identityDerivative.unique (hasFDerivAt_id base)
  apply ContinuousLinearMap.ext
  intro direction
  have evaluated := congrArg
    (fun linear : Space →L[ℝ] Space => linear (coordinates.symm direction)) linearIdentity
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.id_apply] using evaluated

end EulerNonuniqueness.General
