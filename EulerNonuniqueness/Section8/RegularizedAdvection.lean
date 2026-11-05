import EulerNonuniqueness.Section8.RegularizedFlow

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness.RegularizedFlowOn

variable {source : Vorticity} {integrable : Integrable source}
  {scale horizon : ℝ} {positive : 0 < scale}
  (flow : RegularizedFlowOn source integrable scale positive horizon)

theorem continuous_particleMap (time : ℝ) : Continuous (flow.particleMap time) :=
  continuous_id.add (flow.displacement time).continuous

theorem continuousOn_particleTrajectory (label : Plane) :
    ContinuousOn (fun time => flow.particleMap time label) (Icc 0 horizon) :=
  continuousOn_const.add (BoundedContinuousFunction.continuous_eval_const.comp_continuousOn flow.continuous)

theorem hasDerivWithinAt_particleTrajectory {time : ℝ} (inside : time ∈ Icc 0 horizon) (label : Plane) :
    HasDerivWithinAt (fun next => flow.particleMap next label)
      (lagrangianVelocity source (regularizedBiotSavartKernel scale) (flow.displacement time)
        (flow.particleMap time label)) (Icc 0 horizon) time :=
  hasDerivWithinAt_displacement_trajectory integrable
    (lipschitz_regularizedBiotSavartKernel positive).continuous
    (bound := regularizedKernelNormBound positive)
    (fun position => norm_regularizedBiotSavartKernel_le positive position) (flow.equation time inside) label

theorem injective_particleMap {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    Function.Injective (flow.particleMap time) := by
  apply injective_flow_of_lipschitz_ODE
    (field := fun next => lagrangianVelocity source (regularizedBiotSavartKernel scale) (flow.displacement next))
    (flow := flow.particleMap)
    (fun next => lipschitz_lagrangianVelocity integrable (lipschitz_regularizedBiotSavartKernel positive)
      (bound := regularizedKernelNormBound positive)
      (fun position => norm_regularizedBiotSavartKernel_le positive position) (flow.displacement next))
    (fun label => by simp [particleMap, flow.initial])
    flow.continuousOn_particleTrajectory
    (fun label next nextInside => flow.hasDerivWithinAt_particleTrajectory nextInside label) inside

theorem measurableEmbedding_particleMap {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    MeasurableEmbedding (flow.particleMap time) :=
  (flow.continuous_particleMap time).measurable.measurableEmbedding (flow.injective_particleMap inside)

theorem eLpNorm_vorticity (nonnegative : 0 ≤ horizon) {time : ℝ} (inside : time ∈ Icc 0 horizon)
    (exponent : ℝ≥0∞) : eLpNorm (flow.vorticity time) exponent volume = eLpNorm source exponent volume :=
  eLpNorm_injectionAdvection (flow.measurableEmbedding_particleMap inside)
    (flow.map_particleMap nonnegative inside) source exponent

theorem memLp_vorticity (nonnegative : 0 ≤ horizon) {time : ℝ} (inside : time ∈ Icc 0 horizon)
    {exponent : ℝ≥0∞} (member : MemLp source exponent volume) : MemLp (flow.vorticity time) exponent volume :=
  memLp_injectionAdvection (flow.measurableEmbedding_particleMap inside)
    (flow.map_particleMap nonnegative inside) member

theorem integral_vorticity_smul {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (nonnegative : 0 ≤ horizon) {time : ℝ} (inside : time ∈ Icc 0 horizon) (coefficient : Plane → Value) :
    (∫ position, flow.vorticity time position • coefficient position) =
      ∫ label, source label • coefficient (flow.particleMap time label) :=
  integral_injectionAdvection_smul (flow.measurableEmbedding_particleMap inside)
    (flow.map_particleMap nonnegative inside) source coefficient

theorem integral_vorticity (nonnegative : 0 ≤ horizon) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    (∫ position, flow.vorticity time position) = ∫ label, source label := by
  simpa only [smul_eq_mul, mul_one] using flow.integral_vorticity_smul nonnegative inside (fun _ => (1 : ℝ))

theorem vorticity_initial : flow.vorticity 0 = source := by
  have mapInitial : flow.particleMap 0 = id := by
    funext label
    simp [particleMap, flow.initial]
  funext position
  change injectionAdvection (flow.particleMap 0) source position = source position
  rw [mapInitial]
  exact injectionAdvection_apply Function.injective_id source position

end EulerNonuniqueness.RegularizedFlowOn
