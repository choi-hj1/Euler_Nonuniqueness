import EulerNonuniqueness.Section7.PatchObservation

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness.Paper

theorem exists_fixed_observation_of_annular_patch_domains
    {counts : ℕ → ℕ} {scales : Scales}
    {reference alternative : (index : ℕ) → PatchMotion (counts index)}
    (alternativeEvolutions : ∀ index, FinitePatchEvolution scales (alternative index) 1)
    (alternativeDisjoint : ∀ index, PatchesDisjoint (alternative index) 1)
    (outer : ∀ index, Fin (counts index)) (outerIndex : ∀ index, (outer index).val = 0)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (center : Plane) {innerRadius outerRadius : ℝ}
    (innerPositive : 0 < innerRadius) (ordered : innerRadius < outerRadius)
    (referenceInside : ∀ index patch position,
      position ∈ (reference index).domain 1 (outer index) patch → ‖position - center‖ ≤ innerRadius / 2)
    (referenceOthersOutside : ∀ index other, other ≠ outer index → ∀ patch position,
      position ∈ (reference index).domain 1 other patch → 2 * outerRadius ≤ ‖position - center‖)
    (alternativeInside : ∀ index patch position,
      position ∈ (alternative index).domain 1 (outer index) patch →
        innerRadius ≤ ‖position - center‖ ∧ ‖position - center‖ ≤ outerRadius)
    (alternativeOthersOutside : ∀ index other, other ≠ outer index → ∀ patch position,
      position ∈ (alternative index).domain 1 other patch → 2 * outerRadius ≤ ‖position - center‖) :
    ∃ observation : Plane → ℝ, ContDiff ℝ ∞ observation ∧ HasCompactSupport observation ∧
      (∀ position, 0 ≤ observation position ∧ observation position ≤ 1) ∧
      (∀ index, weightedAbsIntegral volume observation (patchVorticity scales (reference index) 1) = 0) ∧
      ∀ index, weightedAbsIntegral volume observation (patchVorticity scales (alternative index) 1) =
        4 * scales.circulation 1 := by
  obtain ⟨observation, smooth, compact, bounded, innerZero, annulusOne, outerZero⟩ :=
    Complex.exists_smooth_annular_cutoff center innerPositive ordered
  refine ⟨observation, smooth, compact, bounded, ?_, ?_⟩
  · intro index
    apply weightedObservation_zero_of_zero_on_domains
    intro other patch position inside
    by_cases isOuter : other = outer index
    · subst other
      exact innerZero position (referenceInside index patch position inside)
    · exact outerZero position (referenceOthersOutside index other isOuter patch position inside)
  · intro index
    have observationIdentity := (alternativeEvolutions index).weightedObservation_outer (alternativeDisjoint index)
      (time := 1) ⟨zero_le_one, le_rfl⟩ (outer index) smooth.continuous.aestronglyMeasurable bounded
      (fun patch position inside => annulusOne position
        (alternativeInside index patch position inside).1 (alternativeInside index patch position inside).2)
      (fun other different patch position inside => outerZero position
        (alternativeOthersOutside index other different patch position inside))
      amplitudePositive frequencyPositive ratioPositive
    simpa only [outerIndex, zero_add] using observationIdentity

end EulerNonuniqueness.Paper
