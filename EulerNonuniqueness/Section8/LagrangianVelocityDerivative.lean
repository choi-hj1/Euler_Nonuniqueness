import EulerNonuniqueness.Section8.LagrangianVelocity
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness

def lagrangianVelocityDerivative (source : Vorticity) (kernel : Velocity)
    (displacement : Plane →ᵇ Plane) (position : Plane) : Plane →L[ℝ] Plane :=
  ∫ label, source label • fderiv ℝ kernel (position - (label + displacement label))

theorem hasFDerivAt_lagrangianVelocity {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (smooth : ContDiff ℝ 1 kernel)
    {bound derivativeBound : ℝ≥0} (bounded : ∀ position, ‖kernel position‖ ≤ bound)
    (derivativeBounded : ∀ position, ‖fderiv ℝ kernel position‖ ≤ derivativeBound)
    (displacement : Plane →ᵇ Plane) (position : Plane) :
    HasFDerivAt (lagrangianVelocity source kernel displacement)
      (lagrangianVelocityDerivative source kernel displacement position) position := by
  have derivativeContinuous : Continuous (fderiv ℝ kernel) := smooth.continuous_fderiv le_rfl
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun point label => source label • kernel (point - (label + displacement label)))
    (F' := fun point label => source label • fderiv ℝ kernel (point - (label + displacement label)))
    (μ := (volume : Measure Plane)) (x₀ := position) (ε := 1)
    (bound := fun label => ‖source label‖ * (derivativeBound : ℝ)) zero_lt_one
  · exact Filter.Eventually.of_forall fun point =>
      (integrable_lagrangianVelocity_integrand integrable smooth.continuous bounded displacement point).aestronglyMeasurable
  · exact integrable_lagrangianVelocity_integrand integrable smooth.continuous bounded displacement position
  · exact integrable.aestronglyMeasurable.smul
      (derivativeContinuous.comp (continuous_const.sub (continuous_id.add displacement.continuous))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun label point _ => by
      exact (norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (derivativeBounded _) (norm_nonneg _))
  · exact integrable.norm.mul_const _
  · exact Filter.Eventually.of_forall fun label point _ => by
      have translation : HasFDerivAt (fun other : Plane => other - (label + displacement label))
          (ContinuousLinearMap.id ℝ Plane) point := (hasFDerivAt_id point).sub_const _
      simpa only [ContinuousLinearMap.comp_id] using
        ((smooth.differentiable le_rfl _).hasFDerivAt.comp point translation).const_smul (source label)

end EulerNonuniqueness
