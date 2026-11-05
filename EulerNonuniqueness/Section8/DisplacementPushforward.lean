import EulerNonuniqueness.Section8.DisplacementJacobian
import EulerNonuniqueness.General.FlowInjectivity
import EulerNonuniqueness.General.UnitJacobianPushforward

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness

theorem map_displacement_flow_eq_restrict_range {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (smooth : ContDiff ℝ 1 kernel)
    {lipschitzBound bound derivativeBound : ℝ≥0}
    (lipschitz : LipschitzWith lipschitzBound kernel)
    (bounded : ∀ position, ‖kernel position‖ ≤ bound)
    (derivativeBounded : ∀ position, ‖fderiv ℝ kernel position‖ ≤ derivativeBound)
    (traceZero : ∀ position, (fderiv ℝ kernel position 1).re +
      (fderiv ℝ kernel position Complex.I).im = 0)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) {path : ℝ → (Plane →ᵇ Plane)}
    (initial : path 0 = 0) (continuous : ContinuousOn path (Icc 0 horizon))
    (equation : ∀ time ∈ Icc 0 horizon, HasDerivWithinAt path
      (displacementVectorField integrable lipschitz.continuous bounded (path time)) (Icc 0 horizon) time)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    Measure.map (fun label => label + path time label) (volume : Measure Plane) =
      volume.restrict (range (fun label => label + path time label)) := by
  have spatialDerivative (label : Plane) :
      HasFDerivAt (fun other => other + path time other)
        (fderiv ℝ (fun other => other + path time other) label) label := by
    obtain ⟨_, _, _, _, derivative⟩ := exists_spatial_displacement_derivative integrable smooth
      lipschitz bounded derivativeBounded nonnegative initial continuous equation label
    exact (derivative time inside).differentiableAt.hasFDerivAt
  have injective : Function.Injective (fun label => label + path time label) :=
    injective_flow_of_lipschitz_ODE
      (field := fun next => lagrangianVelocity source kernel (path next))
      (flow := fun next label => label + path next label)
      (fun next => lipschitz_lagrangianVelocity integrable lipschitz bounded (path next))
      (fun label => by simp [initial])
      (fun label => continuousOn_const.add
        (BoundedContinuousFunction.continuous_eval_const.comp_continuousOn continuous))
      (fun label next nextInside => hasDerivWithinAt_displacement_trajectory integrable
        lipschitz.continuous bounded (equation next nextInside) label) inside
  exact map_eq_restrict_range_of_unit_jacobian volume spatialDerivative injective
    (fun label => det_fderiv_displacement_flow_eq_one integrable smooth lipschitz bounded
      derivativeBounded traceZero nonnegative initial continuous equation label inside)

end EulerNonuniqueness
