import EulerNonuniqueness.Section8.LagrangianVelocityDerivative

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness

theorem continuous_lagrangianVelocityDerivative {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (smooth : ContDiff ℝ 1 kernel)
    {derivativeBound : ℝ≥0}
    (bounded : ∀ position, ‖fderiv ℝ kernel position‖ ≤ derivativeBound) :
    Continuous (fun point : (Plane →ᵇ Plane) × Plane =>
      lagrangianVelocityDerivative source kernel point.1 point.2) := by
  letI : FirstCountableTopology ((Plane →ᵇ Plane) × Plane) :=
    @UniformSpace.firstCountableTopology ((Plane →ᵇ Plane) × Plane) _
      EMetric.instIsCountablyGeneratedUniformity
  have derivativeContinuous : Continuous (fderiv ℝ kernel) := smooth.continuous_fderiv le_rfl
  apply continuous_of_dominated (μ := (volume : Measure Plane))
    (F := fun point : (Plane →ᵇ Plane) × Plane => fun label =>
      source label • fderiv ℝ kernel (point.2 - (label + point.1 label)))
    (bound := fun label => ‖source label‖ * (derivativeBound : ℝ))
  · intro point
    exact integrable.aestronglyMeasurable.smul
      (derivativeContinuous.comp (continuous_const.sub
        (continuous_id.add point.1.continuous))).aestronglyMeasurable
  · intro point
    exact Filter.Eventually.of_forall fun label =>
      (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _))
  · exact integrable.norm.mul_const _
  · exact Filter.Eventually.of_forall fun label => continuous_const.smul
      (derivativeContinuous.comp (continuous_snd.sub (continuous_const.add
        (BoundedContinuousFunction.continuous_eval_const.comp continuous_fst))))

theorem norm_lagrangianVelocityDerivative_le {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) {derivativeBound : ℝ≥0}
    (bounded : ∀ position, ‖fderiv ℝ kernel position‖ ≤ derivativeBound)
    (displacement : Plane →ᵇ Plane) (position : Plane) :
    ‖lagrangianVelocityDerivative source kernel displacement position‖ ≤
      derivativeBound * sourceL1Mass source := by
  calc
    _ ≤ ∫ label, ‖source label‖ * (derivativeBound : ℝ) :=
      norm_integral_le_of_norm_le (integrable.norm.mul_const _)
        (Filter.Eventually.of_forall fun label =>
          (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _)))
    _ = _ := by rw [integral_mul_const]; exact mul_comm _ _

end EulerNonuniqueness
