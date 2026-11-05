import EulerNonuniqueness.Section8.DisplacementFlow
import EulerNonuniqueness.Section8.LagrangianVelocity

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

theorem dist_displacement_trajectories_le {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) {lipschitzBound bound : ℝ≥0}
    (lipschitz : LipschitzWith lipschitzBound kernel) (bounded : ∀ position, ‖kernel position‖ ≤ bound)
    {horizon : ℝ} {path : ℝ → (Plane →ᵇ Plane)} (initial : path 0 = 0)
    (continuous : ContinuousOn path (Icc 0 horizon))
    (derivative : ∀ time ∈ Icc 0 horizon, HasDerivWithinAt path
      (displacementVectorField integrable lipschitz.continuous bounded (path time)) (Icc 0 horizon) time)
    (first second : Plane) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    dist (first + path time first) (second + path time second) ≤
      dist first second * Real.exp ((lipschitzBound * sourceL1Mass source : ℝ≥0) * time) := by
  have trajectoryContinuous (label : Plane) :
      ContinuousOn (fun other => label + path other label) (Icc 0 horizon) :=
    continuousOn_const.add (BoundedContinuousFunction.continuous_eval_const.comp_continuousOn continuous)
  have trajectoryDerivative (label : Plane) (other : ℝ) (otherInside : other ∈ Ico 0 horizon) :
      HasDerivWithinAt (fun next => label + path next label)
        (lagrangianVelocity source kernel (path other) (label + path other label)) (Ici other) other := by
    exact (hasDerivWithinAt_displacement_trajectory integrable lipschitz.continuous bounded
      (derivative other ⟨otherInside.1, otherInside.2.le⟩) label).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem otherInside)
  have estimate := dist_le_of_trajectories_ODE
    (fun other => lipschitz_lagrangianVelocity integrable lipschitz bounded (path other))
    (trajectoryContinuous first) (trajectoryDerivative first)
    (trajectoryContinuous second) (trajectoryDerivative second)
    (δ := dist first second) (by simp [initial]) time inside
  simpa only [sub_zero] using estimate

end EulerNonuniqueness
