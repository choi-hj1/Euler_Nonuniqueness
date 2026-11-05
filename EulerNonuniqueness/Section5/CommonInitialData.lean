import EulerNonuniqueness.Section5.InitialDifference
import EulerNonuniqueness.General.LpPerturbation

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem exists_common_initialDatum_of_cascade_disks (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) (dipoleAngle : ℕ → ℕ → ℝ)
    (reference alternative : (count : ℕ) → PatchMotion (count + 1))
    (initialDisks : ∀ count, CascadeInitialDisks scales orbit sectionTime (dipoleAngle count)
      (reference count) (alternative count))
    (phase unstable : (count : ℕ) → Fin (count + 1) → ℝ) {threshold : ℝ}
    (referenceDisks : ∀ count, ReferenceInitialDisks scales (reference count) (phase count) (unstable count) threshold)
    (thresholdBound : threshold ≤ 1) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioGreaterOne : 1 < scales.ratio)
    (alphaPositive : 0 < scales.alpha) :
    ∃ initial : Vorticity, InitialDatum initial ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧ ∀ exponent : ℝ, 1 ≤ exponent →
        Tendsto (fun step => eLpNorm (patchVorticity scales (reference (subsequence step)) 0 - initial)
          (ENNReal.ofReal exponent) volume) atTop (𝓝 0) ∧
        Tendsto (fun step => eLpNorm (patchVorticity scales (alternative (subsequence step)) 0 - initial)
          (ENNReal.ofReal exponent) volume) atTop (𝓝 0) := by
  obtain ⟨initial, initialDatum, subsequence, increasing, referenceConverges⟩ :=
    exists_common_initialDatum_of_reference_disks scales (tendsto_add_atTop_nat 1) reference phase unstable
      referenceDisks thresholdBound amplitudePositive frequencyPositive ratioGreaterOne alphaPositive
  have referenceMembers (count : ℕ) (exponent : ℝ) :
      MemLp (patchVorticity scales (reference count) 0) (ENNReal.ofReal exponent) volume := by
    rw [reference_initial_vorticity_eq_disk_sum scales (reference count) (phase count) (unstable count)
      threshold (referenceDisks count)]
    exact memLp_finset_sum' _ (fun index _ => diskQuadrupoleDensity_memLp _ _ index _)
  refine ⟨initial, initialDatum, subsequence, increasing, fun exponent exponentBound =>
    ⟨referenceConverges exponent exponentBound, ?_⟩⟩
  have lpBound : 1 ≤ ENNReal.ofReal exponent := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal exponentBound
  have discrepancyConverges :=
    (cascade_initial_difference_tendsto_zero scales orbit sectionTime dipoleAngle reference alternative
      initialDisks phase unstable threshold referenceDisks amplitudePositive frequencyPositive ratioGreaterOne
      alphaPositive exponentBound).comp increasing.tendsto_atTop
  apply tendsto_eLpNorm_sub_of_vanishing_perturbation lpBound
    (fun step => (cascade_initial_difference_Lp_bound scales orbit sectionTime (dipoleAngle (subsequence step))
      (reference (subsequence step)) (alternative (subsequence step)) (initialDisks (subsequence step))
      (phase (subsequence step)) (unstable (subsequence step)) threshold (referenceDisks (subsequence step))
      amplitudePositive exponentBound).1.aestronglyMeasurable)
    (fun step => ((referenceMembers (subsequence step) exponent).sub (initialDatum.2.1 exponent exponentBound)).aestronglyMeasurable)
    discrepancyConverges (referenceConverges exponent exponentBound)

end EulerNonuniqueness.Paper
