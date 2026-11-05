import EulerNonuniqueness.Section8.RegularizedDisplacementFlow
import EulerNonuniqueness.Section8.DisplacementPushforward
import EulerNonuniqueness.Section8.RegularizedKernelDivergence
import EulerNonuniqueness.General.InjectionAdvection

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness

def regularizedKernelNormBound {scale : ℝ} (positive : 0 < scale) : ℝ≥0 :=
  ⟨1 / (2 * Real.pi * scale), by positivity⟩

def regularizedKernelDerivativeBound {scale : ℝ} (positive : 0 < scale) : ℝ≥0 :=
  ⟨3 / (2 * Real.pi * scale ^ 2), by positivity⟩

def regularizedDisplacementField {source : Vorticity} (integrable : Integrable source)
    {scale : ℝ} (positive : 0 < scale) (displacement : Plane →ᵇ Plane) : Plane →ᵇ Plane :=
  displacementVectorField integrable (lipschitz_regularizedBiotSavartKernel positive).continuous
    (bound := regularizedKernelNormBound positive)
    (fun position => norm_regularizedBiotSavartKernel_le positive position) displacement

structure RegularizedFlowOn (source : Vorticity) (integrable : Integrable source)
    (scale : ℝ) (positive : 0 < scale) (horizon : ℝ) where
  displacement : ℝ → (Plane →ᵇ Plane)
  initial : displacement 0 = 0
  continuous : ContinuousOn displacement (Icc 0 horizon)
  equation : ∀ time ∈ Icc 0 horizon, HasDerivWithinAt displacement
    (regularizedDisplacementField integrable positive (displacement time)) (Icc 0 horizon) time
  speed : ∀ time ∈ Icc 0 horizon, ‖displacement time‖ ≤
    (regularizedKernelNormBound positive * sourceL1Mass source : ℝ≥0) * time

noncomputable def regularizedFlowOn {source : Vorticity} (integrable : Integrable source)
    {scale horizon : ℝ} (positive : 0 < scale) (nonnegative : 0 ≤ horizon) :
    RegularizedFlowOn source integrable scale positive horizon := Classical.choice (by
  obtain ⟨path, initial, continuous, equation, speed⟩ := exists_displacement_flow_on_Icc integrable
    (lipschitz_regularizedBiotSavartKernel positive)
    (bound := regularizedKernelNormBound positive)
    (fun position => norm_regularizedBiotSavartKernel_le positive position) nonnegative
  exact ⟨⟨path, initial, continuous, equation, speed⟩⟩)

namespace RegularizedFlowOn

def particleMap {source : Vorticity} {integrable : Integrable source}
    {scale horizon : ℝ} {positive : 0 < scale}
    (flow : RegularizedFlowOn source integrable scale positive horizon) (time : ℝ) (label : Plane) : Plane :=
  label + flow.displacement time label

def vorticity {source : Vorticity} {integrable : Integrable source}
    {scale horizon : ℝ} {positive : 0 < scale}
    (flow : RegularizedFlowOn source integrable scale positive horizon) (time : ℝ) : Vorticity :=
  injectionAdvection (flow.particleMap time) source

theorem derivativeBound {scale : ℝ} (positive : 0 < scale) (position : Plane) :
    ‖fderiv ℝ (regularizedBiotSavartKernel scale) position‖ ≤ regularizedKernelDerivativeBound positive := by
  apply ContinuousLinearMap.opNorm_le_bound _ (regularizedKernelDerivativeBound positive).coe_nonneg
  exact norm_fderiv_regularizedBiotSavartKernel_le positive position

theorem map_particleMap {source : Vorticity} {integrable : Integrable source}
    {scale horizon : ℝ} {positive : 0 < scale}
    (flow : RegularizedFlowOn source integrable scale positive horizon)
    (nonnegative : 0 ≤ horizon) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    Measure.map (flow.particleMap time) (volume : Measure Plane) =
      volume.restrict (range (flow.particleMap time)) := by
  exact map_displacement_flow_eq_restrict_range integrable
    ((contDiff_regularizedBiotSavartKernel positive).of_le (by simp))
    (lipschitz_regularizedBiotSavartKernel positive)
    (bound := regularizedKernelNormBound positive)
    (fun position => norm_regularizedBiotSavartKernel_le positive position)
    (derivativeBound positive) (divergence_regularizedBiotSavartKernel positive)
    nonnegative flow.initial flow.continuous flow.equation inside

end RegularizedFlowOn

end EulerNonuniqueness
