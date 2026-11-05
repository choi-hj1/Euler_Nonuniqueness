import EulerNonuniqueness.Definitions
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

def sourceL1Mass (source : Vorticity) : ℝ≥0 :=
  ⟨∫ position, ‖source position‖, integral_nonneg fun _ => norm_nonneg _⟩

def displacementInteraction (source : Vorticity) (kernel : Velocity) (displacement : Plane →ᵇ Plane) (position : Plane) : Plane :=
  ∫ label, source label • kernel (position - label + displacement position - displacement label)

theorem integrable_displacementInteraction_integrand {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (continuous : Continuous kernel) {bound : ℝ≥0}
    (bounded : ∀ position, ‖kernel position‖ ≤ bound) (displacement : Plane →ᵇ Plane) (position : Plane) :
    Integrable (fun label => source label • kernel (position - label + displacement position - displacement label)) := by
  have kernelContinuous : Continuous (fun label => kernel (position - label + displacement position - displacement label)) :=
    continuous.comp (((continuous_const.sub continuous_id).add continuous_const).sub displacement.continuous)
  apply (integrable.norm.mul_const (bound : ℝ)).mono' (integrable.aestronglyMeasurable.smul kernelContinuous.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun label => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _)

theorem norm_displacementInteraction_le {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) {bound : ℝ≥0} (bounded : ∀ position, ‖kernel position‖ ≤ bound)
    (displacement : Plane →ᵇ Plane) (position : Plane) :
    ‖displacementInteraction source kernel displacement position‖ ≤ bound * sourceL1Mass source := by
  calc
    _ ≤ ∫ label, ‖source label‖ * (bound : ℝ) := norm_integral_le_of_norm_le (integrable.norm.mul_const _) (by
      exact Filter.Eventually.of_forall fun label => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _))
    _ = _ := by rw [integral_mul_const]; exact mul_comm _ _

theorem continuous_displacementInteraction {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (continuous : Continuous kernel) {bound : ℝ≥0}
    (bounded : ∀ position, ‖kernel position‖ ≤ bound) (displacement : Plane →ᵇ Plane) :
    Continuous (displacementInteraction source kernel displacement) := by
  apply continuous_of_dominated (bound := fun label => ‖source label‖ * (bound : ℝ))
  · exact fun position => (integrable_displacementInteraction_integrand integrable continuous bounded displacement position).aestronglyMeasurable
  · intro position
    exact Filter.Eventually.of_forall fun label => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _)
  · exact integrable.norm.mul_const _
  · exact Filter.Eventually.of_forall fun label => continuous_const.smul
      (continuous.comp (((continuous_id.sub continuous_const).add displacement.continuous).sub continuous_const))

def displacementVectorField {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (continuous : Continuous kernel) {bound : ℝ≥0}
    (bounded : ∀ position, ‖kernel position‖ ≤ bound) (displacement : Plane →ᵇ Plane) : Plane →ᵇ Plane :=
  BoundedContinuousFunction.ofNormedAddCommGroup (displacementInteraction source kernel displacement)
    (continuous_displacementInteraction integrable continuous bounded displacement) (bound * sourceL1Mass source)
    (norm_displacementInteraction_le integrable bounded displacement)

theorem norm_displacementVectorField_le {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (continuous : Continuous kernel) {bound : ℝ≥0}
    (bounded : ∀ position, ‖kernel position‖ ≤ bound) (displacement : Plane →ᵇ Plane) :
    ‖displacementVectorField integrable continuous bounded displacement‖ ≤ bound * sourceL1Mass source := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg bound.coe_nonneg (sourceL1Mass source).coe_nonneg)).mpr
  exact norm_displacementInteraction_le integrable bounded displacement

end EulerNonuniqueness
