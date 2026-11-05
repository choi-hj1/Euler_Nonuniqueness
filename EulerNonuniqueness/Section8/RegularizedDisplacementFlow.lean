import EulerNonuniqueness.Section8.DisplacementFlow
import EulerNonuniqueness.Section8.RegularizedKernelLipschitz

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

theorem exists_regularized_displacement_flow {source : Vorticity} (integrable : Integrable source)
    {scale horizon : ℝ} (scalePositive : 0 < scale) (horizonNonnegative : 0 ≤ horizon) :
    ∃ path : ℝ → (Plane →ᵇ Plane), path 0 = 0 ∧ ContinuousOn path (Icc 0 horizon) ∧
      (∀ time ∈ Icc 0 horizon, ∀ label : Plane,
        HasDerivWithinAt (fun other => label + path other label)
          (∫ sourceLabel, source sourceLabel • regularizedBiotSavartKernel scale
            ((label + path time label) - (sourceLabel + path time sourceLabel))) (Icc 0 horizon) time) ∧
      ∀ time ∈ Icc 0 horizon, ‖path time‖ ≤ (1 / (2 * Real.pi * scale)) * sourceL1Mass source * time := by
  let bound : ℝ≥0 := ⟨1 / (2 * Real.pi * scale), by positivity⟩
  have bounded (position : Plane) : ‖regularizedBiotSavartKernel scale position‖ ≤ bound :=
    norm_regularizedBiotSavartKernel_le scalePositive position
  obtain ⟨path, initialEquality, continuous, derivative, speed⟩ := exists_displacement_flow_on_Icc integrable
    (lipschitz_regularizedBiotSavartKernel scalePositive) bounded horizonNonnegative
  refine ⟨path, initialEquality, continuous, ?_, ?_⟩
  · intro time inside label
    exact hasDerivWithinAt_displacement_trajectory integrable
      (lipschitz_regularizedBiotSavartKernel scalePositive).continuous bounded (derivative time inside) label
  · intro time inside
    simpa only [bound, NNReal.coe_mul] using speed time inside

end EulerNonuniqueness
