import EulerNonuniqueness.Section8.SpatialFlowDifferentiability
import EulerNonuniqueness.Section8.LagrangianDivergence

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness

theorem det_fderiv_displacement_flow_eq_one {source : Vorticity} {kernel : Velocity}
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
    (label : Plane) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    LinearMap.det (fderiv ℝ (fun other => other + path time other) label).toLinearMap = 1 := by
  obtain ⟨jacobian, jacobianInitial, jacobianContinuous, jacobianEquation, spatialDerivative⟩ :=
    exists_spatial_displacement_derivative integrable smooth lipschitz bounded derivativeBounded
      nonnegative initial continuous equation label
  rw [(spatialDerivative time inside).fderiv]
  apply Complex.det_eq_one_of_variational_trace_zero
    (coefficient := fun next => lagrangianVelocityDerivative source kernel (path next) (label + path next label))
    jacobianInitial jacobianContinuous
    (fun direction next nextInside =>
      (jacobianEquation direction next ⟨nextInside.1, nextInside.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem nextInside))
    (fun next _ => lagrangianVelocityDerivative_trace_zero integrable smooth derivativeBounded traceZero
      (path next) (label + path next label)) time inside

end EulerNonuniqueness
