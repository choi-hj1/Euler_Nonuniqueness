import EulerNonuniqueness.Section8.RenormalizedMassIdentity
import EulerNonuniqueness.Section8.RenormalizedError
import EulerNonuniqueness.Section8.RenormalizationL2
import EulerNonuniqueness.Section8.MollificationConvergence

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem integrable_renormalization_of_zero
    {source : Vorticity} (integrable : Integrable source)
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization)
    (zero : renormalization 0 = 0) : Integrable (fun position => renormalization (source position)) := by
  obtain ⟨bound, nonnegative, bounded⟩ := admissible.exists_norm_sub_bound
  apply (integrable.norm.const_mul bound).mono'
    (admissible.1.continuous.comp_aestronglyMeasurable integrable.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun position => by simpa only [zero, sub_zero] using bounded (source position) 0

theorem tendsto_integral_renormalized_mollification
    {source : Vorticity} {radius : ℝ}
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp source (ENNReal.ofReal exponent) volume)
    (supported : Function.support source ⊆ Metric.closedBall 0 radius)
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization)
    (zero : renormalization 0 = 0) :
    Tendsto (fun index => ∫ position, renormalization (mollification source index position)) atTop
      (𝓝 (∫ position, renormalization (source position))) := by
  have sourceIntegrable : Integrable source := memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  have sequenceIntegrable (index : ℕ) : Integrable (mollification source index) :=
    (contDiff_mollification sourceIntegrable index).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_mollification supported index)
  obtain ⟨bound, nonnegative, bounded⟩ := admissible.exists_norm_sub_bound
  have convergence := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
    (tendsto_eLpNorm_mollification_sub membership supported (exponent := 1) le_rfl)
  simp only [Function.comp_apply, ENNReal.ofReal_one, ENNReal.toReal_zero] at convergence
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun index => ?_)
    (by simpa only [mul_zero] using (tendsto_const_nhds (x := bound)).mul convergence)
  rw [← integral_sub (integrable_renormalization_of_zero (sequenceIntegrable index) admissible zero)
    (integrable_renormalization_of_zero sourceIntegrable admissible zero)]
  calc
    _ ≤ ∫ position, ‖renormalization (mollification source index position) - renormalization (source position)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ position, bound * ‖mollification source index position - source position‖ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (((sequenceIntegrable index).sub sourceIntegrable).norm.const_mul bound)
      exact Filter.Eventually.of_forall fun position => bounded _ _
    _ = bound * (eLpNorm (mollification source index - source) 1 volume).toReal := by
      rw [integral_const_mul]
      change bound * (∫ position, ‖(mollification source index - source) position‖) = _
      rw [integral_norm_eq_lintegral_enorm ((sequenceIntegrable index).sub sourceIntegrable).aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm]

end EulerNonuniqueness
