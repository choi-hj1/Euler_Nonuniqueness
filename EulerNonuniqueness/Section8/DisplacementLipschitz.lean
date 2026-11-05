import EulerNonuniqueness.Section8.DisplacementInteraction

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

theorem norm_displacementInteraction_sub_le {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) {lipschitzBound bound : ℝ≥0}
    (lipschitz : LipschitzWith lipschitzBound kernel) (bounded : ∀ position, ‖kernel position‖ ≤ bound)
    (first second : Plane →ᵇ Plane) (position : Plane) :
    ‖displacementInteraction source kernel first position - displacementInteraction source kernel second position‖ ≤
      2 * lipschitzBound * sourceL1Mass source * ‖first - second‖ := by
  rw [displacementInteraction, displacementInteraction, ← integral_sub
    (integrable_displacementInteraction_integrand integrable lipschitz.continuous bounded first position)
    (integrable_displacementInteraction_integrand integrable lipschitz.continuous bounded second position)]
  calc
    _ ≤ ∫ label, ‖source label‖ * ((lipschitzBound : ℝ) * (2 * ‖first - second‖)) :=
      norm_integral_le_of_norm_le (integrable.norm.mul_const _) (by
        exact Filter.Eventually.of_forall fun label => by
          rw [← smul_sub, norm_smul]
          apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have kernelEstimate := lipschitz.dist_le_mul
            (position - label + first position - first label) (position - label + second position - second label)
          simp only [dist_eq_norm] at kernelEstimate
          apply kernelEstimate.trans
          apply mul_le_mul_of_nonneg_left ?_ lipschitzBound.coe_nonneg
          have argumentEquality : (position - label + first position - first label) -
              (position - label + second position - second label) = (first position - second position) - (first label - second label) := by abel
          rw [argumentEquality]
          have firstBound := (first - second).norm_coe_le_norm position
          have secondBound := (first - second).norm_coe_le_norm label
          change ‖first position - second position‖ ≤ ‖first - second‖ at firstBound
          change ‖first label - second label‖ ≤ ‖first - second‖ at secondBound
          exact (norm_sub_le _ _).trans (by linarith))
    _ = _ := by
      rw [integral_mul_const]
      change (sourceL1Mass source : ℝ) * ((lipschitzBound : ℝ) * (2 * ‖first - second‖)) = _
      ring

theorem lipschitz_displacementVectorField {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) {lipschitzBound bound : ℝ≥0}
    (lipschitz : LipschitzWith lipschitzBound kernel) (bounded : ∀ position, ‖kernel position‖ ≤ bound) :
    LipschitzWith (2 * lipschitzBound * sourceL1Mass source)
      (displacementVectorField integrable lipschitz.continuous bounded) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm, dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro position
  change ‖displacementInteraction source kernel first position - displacementInteraction source kernel second position‖ ≤ _
  simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
    norm_displacementInteraction_sub_le integrable lipschitz bounded first second position

end EulerNonuniqueness
