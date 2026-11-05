import Mathlib

noncomputable section

open Set Filter
open scoped Topology

theorem exists_coordinatewise_convergent_subsequence_of_common_compact_range
    {Index Value : Type*} [Countable Index] [TopologicalSpace Value] [FirstCountableTopology Value]
    {region : Set Value} (compact : IsCompact region) {sequence : ℕ → Index → Value}
    (inside : ∀ step index, sequence step index ∈ region) :
    ∃ limit : Index → Value, (∀ index, limit index ∈ region) ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧ ∀ index,
        Tendsto (fun step => sequence (subsequence step) index) atTop (𝓝 (limit index)) := by
  letI : CompactSpace region := isCompact_iff_compactSpace.mp compact
  let lifted : ℕ → Index → region := fun step index => ⟨sequence step index, inside step index⟩
  obtain ⟨limit, _, subsequence, increasing, converges⟩ :=
    isCompact_univ.tendsto_subseq (fun step => mem_univ (lifted step))
  refine ⟨fun index => limit index, fun index => (limit index).property, subsequence, increasing, ?_⟩
  intro index
  exact (continuous_subtype_val.comp (continuous_apply index)).continuousAt.tendsto.comp converges
