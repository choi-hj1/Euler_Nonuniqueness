import Mathlib

noncomputable section

open Filter Set
open scoped Topology

theorem continuous_of_sequential_joint_tendsto
    {Domain Value : Type*} [TopologicalSpace Domain] [SequentialSpace Domain]
    [PseudoMetricSpace Value] {sequence : ℕ → Domain → Value} {limit : Domain → Value}
    (joint : ∀ indices : ℕ → ℕ, Tendsto indices atTop atTop →
      ∀ points : ℕ → Domain, ∀ point, Tendsto points atTop (𝓝 point) →
        Tendsto (fun step => sequence (indices step) (points step)) atTop (𝓝 (limit point))) :
    Continuous limit := by
  apply continuous_iff_seqContinuous.mpr
  intro points point converges
  have choices (step : ℕ) : ∃ index : ℕ, step ≤ index ∧
      dist (sequence index (points step)) (limit (points step)) < 1 / ((step : ℝ) + 1) := by
    have pointwise := joint id tendsto_id (fun _ => points step) (points step) tendsto_const_nhds
    have close := (Metric.tendsto_atTop.mp pointwise) (1 / ((step : ℝ) + 1)) (by positivity)
    obtain ⟨cutoff, bounded⟩ := close
    exact ⟨max step cutoff, le_max_left _ _, bounded _ (le_max_right _ _)⟩
  choose indices lower close using choices
  have indexTends := tendsto_atTop_mono lower tendsto_id
  have jointLimit := joint indices indexTends points point converges
  apply jointLimit.congr_dist
  exact squeeze_zero (fun _ => dist_nonneg) (fun step => (close step).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendstoUniformly_of_sequential_joint_tendsto
    {Domain Value : Type*} [TopologicalSpace Domain] [FirstCountableTopology Domain]
    [CompactSpace Domain] [PseudoMetricSpace Value]
    {sequence : ℕ → Domain → Value} {limit : Domain → Value}
    (joint : ∀ indices : ℕ → ℕ, Tendsto indices atTop atTop →
      ∀ points : ℕ → Domain, ∀ point, Tendsto points atTop (𝓝 point) →
        Tendsto (fun step => sequence (indices step) (points step)) atTop (𝓝 (limit point))) :
    TendstoUniformly sequence limit atTop := by
  have continuous := continuous_of_sequential_joint_tendsto joint
  rw [Metric.tendstoUniformly_iff]
  by_contra! failure
  obtain ⟨tolerance, positive, failure⟩ := failure
  have choices (step : ℕ) : ∃ index : ℕ, step ≤ index ∧ ∃ point : Domain,
      tolerance ≤ dist (limit point) (sequence index point) := by
    have frequent : ∃ᶠ index in atTop, ¬ ∀ point : Domain,
        dist (limit point) (sequence index point) < tolerance := by
      exact not_eventually.mp failure
    obtain ⟨index, lower, bad⟩ := frequently_atTop.mp frequent step
    push_neg at bad
    obtain ⟨point, large⟩ := bad
    exact ⟨index, lower, point, large⟩
  choose indices lower points large using choices
  obtain ⟨point, _, extraction, increasing, pointTends⟩ :=
    isCompact_univ.tendsto_subseq (fun step => mem_univ (points step))
  have indexTends := (tendsto_atTop_mono lower tendsto_id).comp increasing.tendsto_atTop
  have jointLimit := joint (indices ∘ extraction) indexTends (points ∘ extraction) point pointTends
  have limitTends := continuous.continuousAt.tendsto.comp pointTends
  have distanceTends : Tendsto
      (fun step => dist (limit (points (extraction step)))
        (sequence (indices (extraction step)) (points (extraction step)))) atTop (𝓝 0) := by
    simpa only [dist_self, Function.comp_def] using limitTends.dist jointLimit
  have upper := distanceTends.eventually (gt_mem_nhds positive)
  obtain ⟨step, bound⟩ := upper.exists
  exact (not_lt_of_ge (large (extraction step))) (by simpa only [dist_self] using bound)
