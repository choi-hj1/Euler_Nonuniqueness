import EulerNonuniqueness.Section8.FiniteFamilyAssembly
import EulerNonuniqueness.Section5.CommonInitialSubfamilies
import EulerNonuniqueness.Section7.FixedAnnularObservation

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness.Paper

theorem nonuniqueness_of_annular_cascade_families
    (scales : Scales) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {truncations : ℕ → ℕ} (truncationsTendsto : Tendsto truncations atTop atTop)
    (reference alternative : (index : ℕ) → PatchMotion (truncations index + 1))
    (referenceEvolutions : ∀ index, FinitePatchEvolution scales (reference index) 1)
    (alternativeEvolutions : ∀ index, FinitePatchEvolution scales (alternative index) 1)
    (alternativeDisjoint : ∀ index, PatchesDisjoint (alternative index) 1)
    (dipoleAngle : ℕ → ℕ → ℝ)
    (initialDisks : ∀ index, CascadeInitialDisks scales orbit sectionTime (dipoleAngle index)
      (reference index) (alternative index))
    (phase unstable : (index : ℕ) → Fin (truncations index + 1) → ℝ) {threshold : ℝ}
    (referenceDisks : ∀ index, ReferenceInitialDisks scales (reference index) (phase index) (unstable index) threshold)
    (thresholdBound : threshold ≤ 1) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioGreaterOne : 1 < scales.ratio)
    (alphaPositive : 0 < scales.alpha) {supportRadius : ℝ} (supportRadiusPositive : 0 < supportRadius)
    (referenceSupported : ∀ index, ∀ time ∈ Icc 0 1,
      support (patchVorticity scales (reference index) time) ⊆ Metric.closedBall 0 supportRadius)
    (alternativeSupported : ∀ index, ∀ time ∈ Icc 0 1,
      support (patchVorticity scales (alternative index) time) ⊆ Metric.closedBall 0 supportRadius)
    (outer : ∀ index, Fin (truncations index + 1)) (outerIndex : ∀ index, (outer index).val = 0)
    (center : Plane) {innerRadius outerRadius : ℝ} (innerPositive : 0 < innerRadius) (ordered : innerRadius < outerRadius)
    (referenceInside : ∀ index patch position,
      position ∈ (reference index).domain 1 (outer index) patch → ‖position - center‖ ≤ innerRadius / 2)
    (referenceOthersOutside : ∀ index other, other ≠ outer index → ∀ patch position,
      position ∈ (reference index).domain 1 other patch → 2 * outerRadius ≤ ‖position - center‖)
    (alternativeInside : ∀ index patch position,
      position ∈ (alternative index).domain 1 (outer index) patch →
        innerRadius ≤ ‖position - center‖ ∧ ‖position - center‖ ≤ outerRadius)
    (alternativeOthersOutside : ∀ index other, other ≠ outer index → ∀ patch position,
      position ∈ (alternative index).domain 1 other patch → 2 * outerRadius ≤ ‖position - center‖) :
    Theorem11 := by
  obtain ⟨observation, smooth, compact, bounded, referenceObserved, alternativeObserved⟩ :=
    exists_fixed_observation_of_annular_patch_domains alternativeEvolutions alternativeDisjoint outer outerIndex
      amplitudePositive frequencyPositive (zero_lt_one.trans ratioGreaterOne) center innerPositive ordered
      referenceInside referenceOthersOutside alternativeInside alternativeOthersOutside
  obtain ⟨initial, datum, subsequence, _, referenceConverges, alternativeConverges⟩ :=
    exists_common_initialDatum_of_cascade_subfamilies scales orbit sectionTime truncationsTendsto dipoleAngle
      reference alternative initialDisks phase unstable referenceDisks thresholdBound amplitudePositive
      frequencyPositive ratioGreaterOne alphaPositive
  have massPositive : 0 < 4 * scales.circulation 1 :=
    mul_pos (by norm_num) (scales.circulation_pos frequencyPositive (zero_lt_one.trans ratioGreaterOne) 1)
  obtain ⟨data⟩ := exists_approximationData_of_finite_patch_families
    (fun index => referenceEvolutions (subsequence index))
    (fun index => alternativeEvolutions (subsequence index))
    amplitudePositive frequencyPositive ratioGreaterOne alphaPositive supportRadiusPositive
    (fun index => referenceSupported (subsequence index)) (fun index => alternativeSupported (subsequence index))
    datum referenceConverges alternativeConverges smooth compact bounded massPositive
    (fun index => referenceObserved (subsequence index)) (fun index => alternativeObserved (subsequence index))
  exact nonuniqueness_of_approximation_data data

end EulerNonuniqueness.Paper
