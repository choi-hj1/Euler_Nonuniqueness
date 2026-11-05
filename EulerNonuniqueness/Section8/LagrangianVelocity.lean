import EulerNonuniqueness.Section8.DisplacementInteraction

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

def lagrangianVelocity (source : Vorticity) (kernel : Velocity) (displacement : Plane →ᵇ Plane) (position : Plane) : Plane :=
  ∫ label, source label • kernel (position - (label + displacement label))

theorem integrable_lagrangianVelocity_integrand {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (continuous : Continuous kernel) {bound : ℝ≥0}
    (bounded : ∀ position, ‖kernel position‖ ≤ bound) (displacement : Plane →ᵇ Plane) (position : Plane) :
    Integrable (fun label => source label • kernel (position - (label + displacement label))) := by
  have kernelContinuous : Continuous (fun label => kernel (position - (label + displacement label))) :=
    continuous.comp (continuous_const.sub (continuous_id.add displacement.continuous))
  apply (integrable.norm.mul_const (bound : ℝ)).mono' (integrable.aestronglyMeasurable.smul kernelContinuous.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun label => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _)

theorem continuous_lagrangianVelocity {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (continuous : Continuous kernel) {bound : ℝ≥0}
    (bounded : ∀ position, ‖kernel position‖ ≤ bound) :
    Continuous (fun point : (Plane →ᵇ Plane) × Plane => lagrangianVelocity source kernel point.1 point.2) := by
  letI : FirstCountableTopology ((Plane →ᵇ Plane) × Plane) :=
    @UniformSpace.firstCountableTopology ((Plane →ᵇ Plane) × Plane) _
      EMetric.instIsCountablyGeneratedUniformity
  apply continuous_of_dominated (μ := (volume : Measure Plane))
    (F := fun point : (Plane →ᵇ Plane) × Plane => fun label => source label • kernel (point.2 - (label + point.1 label)))
    (bound := fun label => ‖source label‖ * (bound : ℝ))
  · exact fun point => (integrable_lagrangianVelocity_integrand integrable continuous bounded point.1 point.2).aestronglyMeasurable
  · intro point
    exact Filter.Eventually.of_forall fun label => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _)
  · exact integrable.norm.mul_const _
  · exact Filter.Eventually.of_forall fun label => continuous_const.smul
      (continuous.comp (continuous_snd.sub (continuous_const.add
        (BoundedContinuousFunction.continuous_eval_const.comp continuous_fst))))

theorem norm_lagrangianVelocity_le {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) {bound : ℝ≥0} (bounded : ∀ position, ‖kernel position‖ ≤ bound)
    (displacement : Plane →ᵇ Plane) (position : Plane) :
    ‖lagrangianVelocity source kernel displacement position‖ ≤ bound * sourceL1Mass source := by
  calc
    _ ≤ ∫ label, ‖source label‖ * (bound : ℝ) := norm_integral_le_of_norm_le (integrable.norm.mul_const _) (by
      exact Filter.Eventually.of_forall fun label => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _))
    _ = _ := by rw [integral_mul_const]; exact mul_comm _ _

theorem lipschitz_lagrangianVelocity {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) {lipschitzBound bound : ℝ≥0}
    (lipschitz : LipschitzWith lipschitzBound kernel) (bounded : ∀ position, ‖kernel position‖ ≤ bound)
    (displacement : Plane →ᵇ Plane) :
    LipschitzWith (lipschitzBound * sourceL1Mass source) (lagrangianVelocity source kernel displacement) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm, dist_eq_norm, lagrangianVelocity, lagrangianVelocity, ← integral_sub
    (integrable_lagrangianVelocity_integrand integrable lipschitz.continuous bounded displacement first)
    (integrable_lagrangianVelocity_integrand integrable lipschitz.continuous bounded displacement second)]
  calc
    _ ≤ ∫ label, ‖source label‖ * ((lipschitzBound : ℝ) * ‖first - second‖) :=
      norm_integral_le_of_norm_le (integrable.norm.mul_const _) (by
        exact Filter.Eventually.of_forall fun label => by
          rw [← smul_sub, norm_smul]
          apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have estimate := lipschitz.dist_le_mul (first - (label + displacement label)) (second - (label + displacement label))
          simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using estimate)
    _ = _ := by
      rw [integral_mul_const]
      change (sourceL1Mass source : ℝ) * ((lipschitzBound : ℝ) * ‖first - second‖) = _
      simp only [NNReal.coe_mul]
      ring

end EulerNonuniqueness
