import EulerNonuniqueness.General.ArzelaAscoli

noncomputable section

open Set Filter
open scoped Topology

namespace BoundedContinuousFunction

theorem isCompact_closure_range_of_equicontinuous_of_common_compact_range
    {Domain Value Index : Type*} [TopologicalSpace Domain] [CompactSpace Domain]
    [MetricSpace Value] {family : Index → Domain →ᵇ Value} {region : Set Value}
    (compact : IsCompact region) (inside : ∀ index point, family index point ∈ region)
    (equicontinuous : Equicontinuous (fun index => (family index : Domain → Value))) :
    IsCompact (closure (range family)) := by
  apply arzela_ascoli region compact
  · rintro field point ⟨index, rfl⟩
    exact inside index point
  · choose index indexed using (fun field : range family => field.property)
    have equality : ((↑) : range family → Domain → Value) =
        (fun field => (family (index field) : Domain → Value)) := by
      funext field point
      exact congrArg (fun function : Domain →ᵇ Value => function point) (indexed field).symm
    rw [equality]
    exact equicontinuous.comp index

theorem exists_uniformly_convergent_subsequence_of_equicontinuous_of_common_compact_range
    {Domain Value : Type*} [TopologicalSpace Domain] [CompactSpace Domain]
    [MetricSpace Value] {sequence : ℕ → Domain →ᵇ Value} {region : Set Value}
    (compact : IsCompact region) (inside : ∀ index point, sequence index point ∈ region)
    (equicontinuous : Equicontinuous (fun index => (sequence index : Domain → Value))) :
    ∃ limit : Domain →ᵇ Value, ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      TendstoUniformly (fun index => sequence (subsequence index)) limit atTop := by
  have compactClosure :=
    isCompact_closure_range_of_equicontinuous_of_common_compact_range compact inside equicontinuous
  obtain ⟨limit, _, subsequence, increasing, converges⟩ :=
    compactClosure.tendsto_subseq (fun index => subset_closure (mem_range_self index))
  exact ⟨limit, subsequence, increasing, tendsto_iff_tendstoUniformly.mp converges⟩

end BoundedContinuousFunction
