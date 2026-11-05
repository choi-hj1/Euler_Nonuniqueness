import EulerNonuniqueness.Section8.LagrangianVariational
import EulerNonuniqueness.Section8.DisplacementFlow
import EulerNonuniqueness.General.FlowDifferentiability

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness

set_option maxHeartbeats 800000 in
theorem exists_spatial_displacement_derivative {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (smooth : ContDiff ℝ 1 kernel)
    {lipschitzBound bound derivativeBound : ℝ≥0}
    (lipschitz : LipschitzWith lipschitzBound kernel)
    (bounded : ∀ position, ‖kernel position‖ ≤ bound)
    (derivativeBounded : ∀ position, ‖fderiv ℝ kernel position‖ ≤ derivativeBound)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) {path : ℝ → (Plane →ᵇ Plane)}
    (initial : path 0 = 0) (continuous : ContinuousOn path (Icc 0 horizon))
    (equation : ∀ time ∈ Icc 0 horizon, HasDerivWithinAt path
      (displacementVectorField integrable lipschitz.continuous bounded (path time)) (Icc 0 horizon) time)
    (label : Plane) :
    ∃ jacobian : ℝ → Plane →L[ℝ] Plane,
      jacobian 0 = ContinuousLinearMap.id ℝ Plane ∧ ContinuousOn jacobian (Icc 0 horizon) ∧
      (∀ direction time, time ∈ Icc 0 horizon →
        HasDerivWithinAt (fun next => jacobian next direction)
          (lagrangianVelocityDerivative source kernel (path time) (label + path time label)
            (jacobian time direction)) (Icc 0 horizon) time) ∧
      ∀ time ∈ Icc 0 horizon,
        HasFDerivAt (fun other => other + path time other) (jacobian time) label := by
  obtain ⟨jacobian, jacobianInitial, jacobianContinuous, jacobianEquation⟩ :=
    exists_lagrangian_variational_on_Icc integrable smooth derivativeBounded nonnegative continuous label
  refine ⟨jacobian, jacobianInitial, jacobianContinuous, jacobianEquation, ?_⟩
  intro time inside
  apply hasFDerivAt_flow_of_variational
    (field := lagrangianVelocity source kernel)
    (fieldDerivative := lagrangianVelocityDerivative source kernel)
    (flow := fun next other => other + path next other)
    (parameter := path) (jacobian := jacobian) (horizon := horizon) (time := time)
    (continuous_lagrangianVelocityDerivative integrable smooth derivativeBounded)
    (fun displacement position => hasFDerivAt_lagrangianVelocity integrable smooth bounded derivativeBounded displacement position)
    (fun displacement => lipschitz_lagrangianVelocity integrable lipschitz bounded displacement)
    continuous (fun other => by simp [initial])
    (fun other => continuousOn_const.add
      (BoundedContinuousFunction.continuous_eval_const.comp_continuousOn continuous))
    (fun other next nextInside =>
      (hasDerivWithinAt_displacement_trajectory integrable lipschitz.continuous bounded
        (equation next ⟨nextInside.1, nextInside.2.le⟩) other).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem nextInside))
    label jacobianInitial jacobianContinuous
    (fun direction next nextInside =>
      (jacobianEquation direction next ⟨nextInside.1, nextInside.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem nextInside)) inside

end EulerNonuniqueness
