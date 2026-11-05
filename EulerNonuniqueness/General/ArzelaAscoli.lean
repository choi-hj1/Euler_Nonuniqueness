import Mathlib

noncomputable section

open Set Filter
open scoped Topology

namespace BoundedContinuousFunction

theorem isCompact_closure_range_of_equicontinuous
    {Domain Value Index : Type*} [TopologicalSpace Domain] [CompactSpace Domain]
    [MetricSpace Value] [ProperSpace Value] {family : Index → Domain →ᵇ Value}
    {center : Value} {bound : ℝ}
    (bounded : ∀ index point, dist (family index point) center ≤ bound)
    (equicontinuous : Equicontinuous (fun index => (family index : Domain → Value))) :
    IsCompact (closure (range family)) := by
  apply arzela_ascoli (Metric.closedBall center bound) (isCompact_closedBall _ _)
  · rintro field point ⟨index, rfl⟩
    exact bounded index point
  · choose index indexed using (fun field : range family => field.property)
    have equal : ((↑) : range family → Domain → Value) =
        (fun field => (family (index field) : Domain → Value)) := by
      funext field point
      exact congrArg (fun function : Domain →ᵇ Value => function point) (indexed field).symm
    rw [equal]
    exact equicontinuous.comp index

theorem exists_uniformly_convergent_subsequence_of_equicontinuous
    {Domain Value : Type*} [TopologicalSpace Domain] [CompactSpace Domain]
    [MetricSpace Value] [ProperSpace Value] {sequence : ℕ → Domain →ᵇ Value}
    {center : Value} {bound : ℝ}
    (bounded : ∀ index point, dist (sequence index point) center ≤ bound)
    (equicontinuous : Equicontinuous (fun index => (sequence index : Domain → Value))) :
    ∃ limit : Domain →ᵇ Value, ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      TendstoUniformly (fun index => sequence (subsequence index)) limit atTop := by
  obtain ⟨limit, _, subsequence, increasing, converges⟩ :=
    (isCompact_closure_range_of_equicontinuous bounded equicontinuous).tendsto_subseq
      (fun index => subset_closure (mem_range_self index))
  exact ⟨limit, subsequence, increasing, tendsto_iff_tendstoUniformly.mp converges⟩

end BoundedContinuousFunction

namespace ContinuousMap

theorem isCompact_closure_range_of_equicontinuous
    {Domain Value Index : Type*} [TopologicalSpace Domain]
    [WeaklyLocallyCompactSpace Domain] [MetricSpace Value] [ProperSpace Value]
    {family : Index → C(Domain, Value)}
    (equicontinuous : Equicontinuous (fun index => (family index : Domain → Value)))
    (pointwiseBounded : ∀ point, ∃ center : Value, ∃ bound : ℝ,
      ∀ index, dist (family index point) center ≤ bound) :
    IsCompact (closure (range family)) := by
  letI : T2Space (UniformOnFun Domain Value {compactSet : Set Domain | IsCompact compactSet}) :=
    UniformOnFun.t2Space_of_covering (eq_univ_iff_forall.mpr (fun point =>
      mem_sUnion_of_mem (mem_singleton point) isCompact_singleton))
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun field : C(Domain, Value) => (field : Domain → Value))
    (fun _ compact => compact) isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  · intro compactSet compact
    choose index indexed using (fun field : range family => field.property)
    have equal : ((fun field : C(Domain, Value) => (field : Domain → Value)) ∘
        ((↑) : range family → C(Domain, Value))) =
        (fun field => (family (index field) : Domain → Value)) := by
      funext field point
      exact congrArg (fun function : C(Domain, Value) => function point) (indexed field).symm
    rw [equal]
    exact (equicontinuous.comp index).equicontinuousOn compactSet
  · intro compactSet compact point inside
    obtain ⟨center, bound, bounded⟩ := pointwiseBounded point
    refine ⟨Metric.closedBall center bound, isCompact_closedBall _ _, ?_⟩
    rintro field ⟨index, rfl⟩
    exact bounded index

theorem exists_locally_uniformly_convergent_subsequence_of_equicontinuous
    {Domain Value : Type*} [TopologicalSpace Domain]
    [WeaklyLocallyCompactSpace Domain] [SigmaCompactSpace Domain]
    [MetricSpace Value] [ProperSpace Value] {sequence : ℕ → C(Domain, Value)}
    (equicontinuous : Equicontinuous (fun index => (sequence index : Domain → Value)))
    (pointwiseBounded : ∀ point, ∃ center : Value, ∃ bound : ℝ,
      ∀ index, dist (sequence index point) center ≤ bound) :
    ∃ limit : C(Domain, Value), ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      TendstoLocallyUniformly (fun index => sequence (subsequence index)) limit atTop := by
  obtain ⟨limit, _, subsequence, increasing, converges⟩ :=
    (isCompact_closure_range_of_equicontinuous equicontinuous pointwiseBounded).tendsto_subseq
      (fun index => subset_closure (mem_range_self index))
  exact ⟨limit, subsequence, increasing, tendsto_iff_tendstoLocallyUniformly.mp converges⟩

end ContinuousMap
