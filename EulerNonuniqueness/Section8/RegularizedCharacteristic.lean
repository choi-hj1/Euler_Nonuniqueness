import EulerNonuniqueness.Section8.RegularizedAdvectionVelocity
import EulerNonuniqueness.Section8.TestBounds

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness.RegularizedFlowOn

variable {source : Vorticity} {integrable : Integrable source}
  {scale horizon : ℝ} {positive : 0 < scale}
  (flow : RegularizedFlowOn source integrable scale positive horizon)

theorem characteristic_test_FTC (nonnegative : 0 ≤ horizon)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ 1 test)
    (terminal : ∀ position, test (horizon, position) = 0) (label : Plane) :
    (∫ time in Ioo 0 horizon,
      timeDerivative test (time, flow.particleMap time label) +
        spatialDerivative test (time, flow.particleMap time label)
          (regularizedBiotSavart scale (flow.vorticity time) (flow.particleMap time label))) +
      test (0, label) = 0 := by
  let velocity := fun time => lagrangianVelocity source (regularizedBiotSavartKernel scale)
    (flow.displacement time) (flow.particleMap time label)
  let derivative := fun time => fderiv ℝ test (time, flow.particleMap time label) (1, velocity time)
  have pointContinuous : ContinuousOn (fun time => (time, flow.particleMap time label)) (Icc 0 horizon) :=
    continuousOn_id.prodMk (flow.continuousOn_particleTrajectory label)
  have velocityContinuous : ContinuousOn velocity (Icc 0 horizon) :=
    (continuous_lagrangianVelocity integrable (lipschitz_regularizedBiotSavartKernel positive).continuous
      (bound := regularizedKernelNormBound positive)
      (fun position => norm_regularizedBiotSavartKernel_le positive position)).comp_continuousOn
        (f := fun time => (flow.displacement time, flow.particleMap time label))
        (flow.continuous.prodMk (flow.continuousOn_particleTrajectory label))
  have derivativeContinuous : ContinuousOn derivative (Icc 0 horizon) :=
    ((smooth.continuous_fderiv le_rfl).comp_continuousOn
      (f := fun time => (time, flow.particleMap time label)) pointContinuous).clm_apply
        (continuousOn_const.prodMk velocityContinuous)
  have compositionDerivative (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      HasDerivWithinAt (fun next => test (next, flow.particleMap next label))
        (derivative time) (Icc 0 horizon) time := by
    have trajectory := (hasDerivWithinAt_id time (Icc 0 horizon)).prodMk
      (flow.hasDerivWithinAt_particleTrajectory inside label)
    exact (smooth.differentiable le_rfl _).hasFDerivAt.comp_hasDerivWithinAt time trajectory
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le nonnegative
    (smooth.continuous.comp_continuousOn (f := fun time => (time, flow.particleMap time label)) pointContinuous)
    (fun time inside => (compositionDerivative time ⟨inside.1.le, inside.2.le⟩).hasDerivAt
      (Icc_mem_nhds inside.1 inside.2))
    (derivativeContinuous.intervalIntegrable_of_Icc nonnegative)
  rw [intervalIntegral.integral_of_le nonnegative, integral_Ioc_eq_integral_Ioo] at identity
  have initial : test (0, flow.particleMap 0 label) = test (0, label) := by
    simp [particleMap, flow.initial]
  dsimp only [Function.comp_apply] at identity
  rw [terminal, initial, zero_sub] at identity
  have coefficients : (fun time => timeDerivative test (time, flow.particleMap time label) +
      spatialDerivative test (time, flow.particleMap time label)
        (regularizedBiotSavart scale (flow.vorticity time) (flow.particleMap time label))) =ᵐ[volume.restrict (Ioo 0 horizon)] derivative := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
    rw [flow.regularizedBiotSavart_vorticity nonnegative ⟨inside.1.le, inside.2.le⟩]
    change fderiv ℝ test (time, flow.particleMap time label) (1, 0) +
      fderiv ℝ test (time, flow.particleMap time label) (0, velocity time) =
        fderiv ℝ test (time, flow.particleMap time label) (1, velocity time)
    rw [← map_add]
    congr 1
    simp
  rw [integral_congr_ae coefficients, identity]
  exact neg_add_cancel _

end EulerNonuniqueness.RegularizedFlowOn
