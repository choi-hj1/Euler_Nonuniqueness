import EulerNonuniqueness.Section5.CommonInitialData
import EulerNonuniqueness.Section8.CompactnessStatement

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem cascade_initial_difference_tendsto_zero_subfamily (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) {truncations : ℕ → ℕ}
    (truncationsTendsto : Tendsto truncations atTop atTop) (dipoleAngle : ℕ → ℕ → ℝ)
    (reference alternative : (index : ℕ) → PatchMotion (truncations index + 1))
    (initialDisks : ∀ index, CascadeInitialDisks scales orbit sectionTime (dipoleAngle index)
      (reference index) (alternative index))
    (phase unstable : (index : ℕ) → Fin (truncations index + 1) → ℝ) (threshold : ℝ)
    (referenceDisks : ∀ index, ReferenceInitialDisks scales (reference index) (phase index) (unstable index) threshold)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioGreaterOne : 1 < scales.ratio) (alphaPositive : 0 < scales.alpha)
    {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    Tendsto (fun index => eLpNorm (patchVorticity scales (alternative index) 0 -
      patchVorticity scales (reference index) 0) (ENNReal.ofReal exponent) volume) atTop (𝓝 0) := by
  have properties (index : ℕ) := cascade_initial_difference_Lp_bound scales orbit sectionTime (dipoleAngle index)
    (reference index) (alternative index) (initialDisks index) (phase index) (unstable index) threshold
    (referenceDisks index) amplitudePositive exponentBound
  have envelopeTendsto := (scales.patch_Lp_envelope_summable amplitudePositive frequencyPositive ratioGreaterOne
    alphaPositive (zero_lt_one.trans_le exponentBound)).tendsto_atTop_zero.comp
      ((tendsto_add_atTop_nat 1).comp truncationsTendsto)
  have realConverges : Tendsto (fun index =>
      (eLpNorm (patchVorticity scales (alternative index) 0 - patchVorticity scales (reference index) 0)
        (ENNReal.ofReal exponent) volume).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun index => (properties index).2)
      (by simpa only [mul_zero] using envelopeTendsto.const_mul 8)
  have ennrealConverges := ENNReal.continuous_ofReal.continuousAt.tendsto.comp realConverges
  change Tendsto (fun index => ENNReal.ofReal
    (eLpNorm (patchVorticity scales (alternative index) 0 - patchVorticity scales (reference index) 0)
      (ENNReal.ofReal exponent) volume).toReal) atTop (𝓝 (ENNReal.ofReal 0)) at ennrealConverges
  have equal (index : ℕ) := ENNReal.ofReal_toReal (properties index).1.eLpNorm_lt_top.ne
  simpa only [equal, ENNReal.ofReal_zero] using ennrealConverges

theorem exists_common_initialDatum_of_cascade_subfamilies (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) {truncations : ℕ → ℕ}
    (truncationsTendsto : Tendsto truncations atTop atTop) (dipoleAngle : ℕ → ℕ → ℝ)
    (reference alternative : (index : ℕ) → PatchMotion (truncations index + 1))
    (initialDisks : ∀ index, CascadeInitialDisks scales orbit sectionTime (dipoleAngle index)
      (reference index) (alternative index))
    (phase unstable : (index : ℕ) → Fin (truncations index + 1) → ℝ) {threshold : ℝ}
    (referenceDisks : ∀ index, ReferenceInitialDisks scales (reference index) (phase index) (unstable index) threshold)
    (thresholdBound : threshold ≤ 1) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioGreaterOne : 1 < scales.ratio)
    (alphaPositive : 0 < scales.alpha) :
    ∃ initial : Vorticity, InitialDatum initial ∧ ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      InitialLpConvergence (fun index => patchVorticity scales (reference (subsequence index))) initial ∧
      InitialLpConvergence (fun index => patchVorticity scales (alternative (subsequence index))) initial := by
  obtain ⟨initial, datum, subsequence, increasing, referenceConverges⟩ :=
    exists_common_initialDatum_of_reference_disks scales ((tendsto_add_atTop_nat 1).comp truncationsTendsto)
      reference phase unstable referenceDisks thresholdBound amplitudePositive frequencyPositive ratioGreaterOne alphaPositive
  refine ⟨initial, datum, subsequence, increasing, ⟨datum.2.1, referenceConverges⟩, datum.2.1, ?_⟩
  intro exponent exponentBound
  have lpBound : 1 ≤ ENNReal.ofReal exponent := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal exponentBound
  have differenceConverges := (cascade_initial_difference_tendsto_zero_subfamily scales orbit sectionTime
    truncationsTendsto dipoleAngle reference alternative initialDisks phase unstable threshold referenceDisks
      amplitudePositive frequencyPositive ratioGreaterOne alphaPositive exponentBound).comp increasing.tendsto_atTop
  have referenceMembers (index : ℕ) :
      MemLp (patchVorticity scales (reference index) 0) (ENNReal.ofReal exponent) volume := by
    rw [reference_initial_vorticity_eq_disk_sum scales (reference index) (phase index) (unstable index)
      threshold (referenceDisks index)]
    exact memLp_finset_sum' _ (fun index _ => diskQuadrupoleDensity_memLp _ _ index _)
  apply tendsto_eLpNorm_sub_of_vanishing_perturbation lpBound
    (fun index => (cascade_initial_difference_Lp_bound scales orbit sectionTime (dipoleAngle (subsequence index))
      (reference (subsequence index)) (alternative (subsequence index)) (initialDisks (subsequence index))
      (phase (subsequence index)) (unstable (subsequence index)) threshold (referenceDisks (subsequence index))
      amplitudePositive exponentBound).1.aestronglyMeasurable)
    (fun index => ((referenceMembers (subsequence index)).sub (datum.2.1 exponent exponentBound)).aestronglyMeasurable)
    differenceConverges (referenceConverges exponent exponentBound)

end EulerNonuniqueness.Paper
