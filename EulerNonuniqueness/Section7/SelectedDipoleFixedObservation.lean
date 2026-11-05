import EulerNonuniqueness.Section7.SelectedPatchObservation

noncomputable section

open MeasureTheory Set Filter Function Metric
open scoped Topology ContDiff

namespace EulerNonuniqueness.Paper

theorem exists_fixed_observation_of_selected_dipole_domains
    {counts : ℕ → ℕ} {scales : Scales}
    {reference alternative : (index : ℕ) → PatchMotion (counts index)}
    (alternativeEvolutions : ∀ index, FinitePatchEvolution scales (alternative index) 1)
    (alternativeDisjoint : ∀ index, PatchesDisjoint (alternative index) 1)
    (outer : ∀ index, Fin (counts index)) (outerIndex : ∀ index, (outer index).val = 0)
    (selected : (index : ℕ) → Finset (Fin (counts index) × Fin 4))
    (selectedOuter : ∀ index pair, pair ∈ selected index → pair.1 = outer index)
    (selectedCard : ∀ index, (selected index).card = 2)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) {length bound : ℝ} (lengthPositive : 0 < length)
    (centers : ℕ → Plane) (centersBounded : ∀ index, ‖centers index‖ ≤ bound)
    (referenceFar : ∀ index other patch position,
      position ∈ (reference index).domain 1 other patch → 4 * length ≤ ‖position - centers index‖)
    (selectedAnnulus : ∀ index pair, pair ∈ selected index → ∀ position,
      position ∈ (alternative index).domain 1 pair.1 pair.2 →
        length / 3 ≤ ‖position - centers index‖ ∧ ‖position - centers index‖ ≤ 3 * length / 4)
    (alternativeOthersFar : ∀ index pair, pair ∉ selected index → ∀ position,
      position ∈ (alternative index).domain 1 pair.1 pair.2 → 4 * length ≤ ‖position - centers index‖) :
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      ∃ observation : Plane → ℝ, ContDiff ℝ ∞ observation ∧ HasCompactSupport observation ∧
        (∀ position, 0 ≤ observation position ∧ observation position ≤ 1) ∧
        (∀ index, weightedAbsIntegral volume observation (patchVorticity scales (reference (subsequence index)) 1) = 0) ∧
        ∀ index, weightedAbsIntegral volume observation (patchVorticity scales (alternative (subsequence index)) 1) =
          2 * scales.circulation 1 := by
  obtain ⟨center, _, subsequence, increasing, converges⟩ := (isCompact_closedBall (0 : Plane) bound).tendsto_subseq
    (fun index => by simpa only [mem_closedBall, dist_zero_right] using centersBounded index)
  obtain ⟨cutoff, close⟩ := Metric.tendsto_atTop.1 converges (length / 24) (by positivity)
  let retained := fun index => subsequence (index + cutoff)
  have retainedIncreasing : StrictMono retained := increasing.comp (fun _ _ less => Nat.add_lt_add_right less cutoff)
  have centerClose (index : ℕ) : ‖centers (retained index) - center‖ ≤ length / 24 := by
    apply le_of_lt
    simpa only [retained, dist_eq_norm] using close (index + cutoff) (by omega)
  obtain ⟨observation, smooth, compact, bounded, _, oneOn, zeroOn⟩ :=
    Complex.exists_smooth_annular_cutoff center (show 0 < length / 4 by positivity) (show length / 4 < length by linarith)
  have far (index : ℕ) (position : Plane) (distance : 4 * length ≤ ‖position - centers (retained index)‖) :
      2 * length ≤ ‖position - center‖ := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub position center (centers (retained index))
    rw [norm_sub_rev center] at triangle
    linarith [centerClose index]
  refine ⟨retained, retainedIncreasing, observation, smooth, compact, bounded, ?_, ?_⟩
  · intro index
    exact weightedObservation_zero_of_zero_on_domains scales (reference (retained index)) 1
      (fun other patch position inside => zeroOn position (far index position (referenceFar (retained index) other patch position inside)))
  · intro index
    have observed := (alternativeEvolutions (retained index)).weightedObservation_selected_patches
      (alternativeDisjoint (retained index)) (time := 1) ⟨zero_le_one, le_rfl⟩ (selected (retained index)) (outer (retained index))
      (selectedOuter (retained index)) smooth.continuous.aestronglyMeasurable bounded
      (fun pair member position inside => by
        have bounds := selectedAnnulus (retained index) pair member position inside
        have upper := norm_sub_le_norm_sub_add_norm_sub position (centers (retained index)) center
        have lower := norm_sub_le_norm_sub_add_norm_sub position center (centers (retained index))
        rw [norm_sub_rev center] at lower
        apply oneOn position <;> linarith [centerClose index])
      (fun pair outside position inside => zeroOn position (far index position
        (alternativeOthersFar (retained index) pair outside position inside)))
      amplitudePositive frequencyPositive ratioPositive
    simpa only [selectedCard, outerIndex, zero_add, Nat.cast_ofNat] using observed

end EulerNonuniqueness.Paper
