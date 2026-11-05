import EulerNonuniqueness.Section7.SelectedDipoleFixedObservation
import EulerNonuniqueness.Section5.CommonInitialSubfamilies
import EulerNonuniqueness.Section8.FiniteFamilyAssembly

noncomputable section

open MeasureTheory Set Filter Function Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_approximationData_of_selected_dipole_cascade_families
    (scales : Scales) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {truncations : ℕ → ℕ} (truncationsTendsto : Tendsto truncations atTop atTop)
    (dipoleAngle : ℕ → ℕ → ℝ)
    (reference alternative : (index : ℕ) → PatchMotion (truncations index + 1))
    (initialDisks : ∀ index, CascadeInitialDisks scales orbit sectionTime (dipoleAngle index)
      (reference index) (alternative index))
    (phase unstable : (index : ℕ) → Fin (truncations index + 1) → ℝ) {threshold : ℝ}
    (referenceDisks : ∀ index, ReferenceInitialDisks scales (reference index) (phase index) (unstable index) threshold)
    (thresholdBound : threshold ≤ 1) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioGreaterOne : 1 < scales.ratio)
    (alphaPositive : 0 < scales.alpha)
    (referenceEvolutions : ∀ index, FinitePatchEvolution scales (reference index) 1)
    (alternativeEvolutions : ∀ index, FinitePatchEvolution scales (alternative index) 1)
    (alternativeDisjoint : ∀ index, PatchesDisjoint (alternative index) 1)
    {radius : ℝ} (radiusPositive : 0 < radius)
    (referenceSupported : ∀ index, ∀ time ∈ Icc 0 1,
      support (patchVorticity scales (reference index) time) ⊆ closedBall 0 radius)
    (alternativeSupported : ∀ index, ∀ time ∈ Icc 0 1,
      support (patchVorticity scales (alternative index) time) ⊆ closedBall 0 radius)
    (outer : ∀ index, Fin (truncations index + 1)) (outerIndex : ∀ index, (outer index).val = 0)
    (selected : (index : ℕ) → Finset (Fin (truncations index + 1) × Fin 4))
    (selectedOuter : ∀ index pair, pair ∈ selected index → pair.1 = outer index)
    (selectedCard : ∀ index, (selected index).card = 2)
    {length bound : ℝ} (lengthPositive : 0 < length)
    (centers : ℕ → Plane) (centersBounded : ∀ index, ‖centers index‖ ≤ bound)
    (referenceFar : ∀ index other patch position,
      position ∈ (reference index).domain 1 other patch → 4 * length ≤ ‖position - centers index‖)
    (selectedAnnulus : ∀ index pair, pair ∈ selected index → ∀ position,
      position ∈ (alternative index).domain 1 pair.1 pair.2 →
        length / 3 ≤ ‖position - centers index‖ ∧ ‖position - centers index‖ ≤ 3 * length / 4)
    (alternativeOthersFar : ∀ index pair, pair ∉ selected index → ∀ position,
      position ∈ (alternative index).domain 1 pair.1 pair.2 → 4 * length ≤ ‖position - centers index‖) :
    Nonempty ApproximationData := by
  obtain ⟨observed, observedIncreasing, observation, smooth, compact, bounded, referenceObserved, alternativeObserved⟩ :=
    exists_fixed_observation_of_selected_dipole_domains alternativeEvolutions alternativeDisjoint outer outerIndex selected
      selectedOuter selectedCard amplitudePositive frequencyPositive (by linarith) lengthPositive centers centersBounded
      referenceFar selectedAnnulus alternativeOthersFar
  obtain ⟨initial, datum, retained, retainedIncreasing, referenceConverges, alternativeConverges⟩ :=
    exists_common_initialDatum_of_cascade_subfamilies scales orbit sectionTime
      (truncationsTendsto.comp observedIncreasing.tendsto_atTop) (fun index => dipoleAngle (observed index))
      (fun index => reference (observed index)) (fun index => alternative (observed index))
      (fun index => initialDisks (observed index)) (fun index => phase (observed index))
      (fun index => unstable (observed index)) (fun index => referenceDisks (observed index))
      thresholdBound amplitudePositive frequencyPositive ratioGreaterOne alphaPositive
  exact exists_approximationData_of_finite_patch_families
    (fun index => referenceEvolutions (observed (retained index)))
    (fun index => alternativeEvolutions (observed (retained index)))
    amplitudePositive frequencyPositive ratioGreaterOne alphaPositive radiusPositive
    (fun index => referenceSupported (observed (retained index)))
    (fun index => alternativeSupported (observed (retained index))) datum referenceConverges alternativeConverges
    smooth compact bounded (mul_pos (by norm_num) (scales.circulation_pos frequencyPositive (by linarith) 1))
    (fun index => referenceObserved (retained index)) (fun index => alternativeObserved (retained index))

end EulerNonuniqueness.Paper
