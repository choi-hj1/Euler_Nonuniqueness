import Mathlib

noncomputable section

open Set Filter
open scoped Topology

theorem isCompact_closure_of_exists_convergent_subsequence
    {Value : Type*} [PseudoMetricSpace Value] {region : Set Value}
    (subsequences : ∀ sequence : ℕ → Value, (∀ index, sequence index ∈ region) →
      ∃ limit : Value, ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        Tendsto (sequence ∘ subsequence) atTop (𝓝 limit)) :
    IsCompact (closure region) := by
  apply IsSeqCompact.isCompact
  intro sequence inside
  have approximation (index : ℕ) : ∃ point ∈ region,
      dist (sequence index) point < 1 / ((index : ℝ) + 1) :=
    Metric.mem_closure_iff.mp (inside index) _ (by positivity)
  choose approximations approximationInside close using approximation
  obtain ⟨limit, subsequence, increasing, converges⟩ := subsequences approximations approximationInside
  have limitInside : limit ∈ closure region := isClosed_closure.mem_of_tendsto converges
    (Eventually.of_forall fun index => subset_closure (approximationInside (subsequence index)))
  refine ⟨limit, limitInside, subsequence, increasing, ?_⟩
  have error : Tendsto (fun index => dist (sequence index) (approximations index)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun index => (close index).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  filter_upwards [(error.comp increasing.tendsto_atTop).eventually
    (gt_mem_nhds (half_pos positive)),
    Metric.tendsto_nhds.mp converges (tolerance / 2) (half_pos positive)] with index near limitNear
  have triangle := dist_triangle (sequence (subsequence index))
    (approximations (subsequence index)) limit
  change dist (sequence (subsequence index)) limit < tolerance
  change dist (sequence (subsequence index)) (approximations (subsequence index)) < tolerance / 2 at near
  change dist (approximations (subsequence index)) limit < tolerance / 2 at limitNear
  linarith
