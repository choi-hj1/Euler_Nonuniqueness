import EulerNonuniqueness.Section8.LagrangianVelocityDerivativeContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness

def planeTraceCLM : (Plane →L[ℝ] Plane) →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.apply ℝ Plane 1) +
    Complex.imCLM.comp (ContinuousLinearMap.apply ℝ Plane Complex.I)

theorem planeTraceCLM_apply (linear : Plane →L[ℝ] Plane) :
    planeTraceCLM linear = (linear 1).re + (linear Complex.I).im := rfl

theorem integrable_lagrangianVelocityDerivative_integrand {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (smooth : ContDiff ℝ 1 kernel)
    {derivativeBound : ℝ≥0} (bounded : ∀ position, ‖fderiv ℝ kernel position‖ ≤ derivativeBound)
    (displacement : Plane →ᵇ Plane) (position : Plane) :
    Integrable (fun label => source label • fderiv ℝ kernel (position - (label + displacement label))) := by
  have derivativeContinuous : Continuous (fderiv ℝ kernel) := smooth.continuous_fderiv le_rfl
  have measurable : AEStronglyMeasurable
      (fun label => source label • fderiv ℝ kernel (position - (label + displacement label))) :=
    integrable.aestronglyMeasurable.smul
      (derivativeContinuous.comp (continuous_const.sub
        (continuous_id.add displacement.continuous))).aestronglyMeasurable
  apply (integrable.norm.mul_const (derivativeBound : ℝ)).mono' measurable
  exact Filter.Eventually.of_forall fun label =>
    (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _))

theorem lagrangianVelocityDerivative_trace_zero {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (smooth : ContDiff ℝ 1 kernel)
    {derivativeBound : ℝ≥0} (bounded : ∀ position, ‖fderiv ℝ kernel position‖ ≤ derivativeBound)
    (traceZero : ∀ position, (fderiv ℝ kernel position 1).re +
      (fderiv ℝ kernel position Complex.I).im = 0)
    (displacement : Plane →ᵇ Plane) (position : Plane) :
    (lagrangianVelocityDerivative source kernel displacement position 1).re +
      (lagrangianVelocityDerivative source kernel displacement position Complex.I).im = 0 := by
  change planeTraceCLM (∫ label, source label • fderiv ℝ kernel (position - (label + displacement label))) = 0
  rw [← planeTraceCLM.integral_comp_comm
    (integrable_lagrangianVelocityDerivative_integrand integrable smooth bounded displacement position)]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun label => by
    change planeTraceCLM (source label • fderiv ℝ kernel (position - (label + displacement label))) = 0
    rw [map_smul, planeTraceCLM_apply, traceZero, smul_zero]

end EulerNonuniqueness
