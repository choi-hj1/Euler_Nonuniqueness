import EulerNonuniqueness.Section8.LagrangianVelocityDerivativeContinuity
import EulerNonuniqueness.General.PlaneVariationalExistence

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness

theorem exists_lagrangian_variational_on_Icc {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (smooth : ContDiff ℝ 1 kernel)
    {derivativeBound : ℝ≥0}
    (bounded : ∀ position, ‖fderiv ℝ kernel position‖ ≤ derivativeBound)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) {path : ℝ → (Plane →ᵇ Plane)}
    (continuous : ContinuousOn path (Icc 0 horizon)) (label : Plane) :
    ∃ jacobian : ℝ → Plane →L[ℝ] Plane,
      jacobian 0 = ContinuousLinearMap.id ℝ Plane ∧ ContinuousOn jacobian (Icc 0 horizon) ∧
      ∀ direction time, time ∈ Icc 0 horizon →
        HasDerivWithinAt (fun next => jacobian next direction)
          (lagrangianVelocityDerivative source kernel (path time) (label + path time label)
            (jacobian time direction)) (Icc 0 horizon) time := by
  have trajectoryContinuous : ContinuousOn (fun time => label + path time label) (Icc 0 horizon) :=
    continuousOn_const.add (BoundedContinuousFunction.continuous_eval_const.comp_continuousOn continuous)
  have coefficientContinuous : ContinuousOn
      (fun time => lagrangianVelocityDerivative source kernel (path time) (label + path time label))
      (Icc 0 horizon) :=
    (continuous_lagrangianVelocityDerivative integrable smooth bounded).comp_continuousOn
      (f := fun time => (path time, label + path time label))
      (continuous.prodMk trajectoryContinuous)
  exact exists_plane_variational_on_Icc
    (coefficient := fun time => lagrangianVelocityDerivative source kernel (path time) (label + path time label))
    nonnegative coefficientContinuous
    (bound := derivativeBound * sourceL1Mass source)
    (fun time _ => by simpa only [NNReal.coe_mul] using
      norm_lagrangianVelocityDerivative_le integrable bounded (path time) (label + path time label))

end EulerNonuniqueness
