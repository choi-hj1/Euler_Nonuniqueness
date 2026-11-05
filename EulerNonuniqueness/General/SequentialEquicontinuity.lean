import Mathlib

noncomputable section

open Filter
open scoped Topology

theorem uniformEquicontinuous_of_dist_tendsto_zero
    {Domain Value Index : Type*} [PseudoMetricSpace Domain] [PseudoMetricSpace Value]
    {family : Index → Domain → Value}
    (sequential : ∀ indices : ℕ → Index, ∀ first second : ℕ → Domain,
      Tendsto (fun step => dist (first step) (second step)) atTop (𝓝 0) →
      Tendsto (fun step => dist (family (indices step) (first step))
        (family (indices step) (second step))) atTop (𝓝 0)) :
    UniformEquicontinuous family := by
  rw [Metric.uniformEquicontinuous_iff]
  by_contra! failure
  obtain ⟨tolerance, positive, failure⟩ := failure
  have counterexamples (step : ℕ) : ∃ first second : Domain,
      dist first second < 1 / ((step : ℝ) + 1) ∧
        ∃ index : Index, tolerance ≤ dist (family index first) (family index second) :=
    failure (1 / ((step : ℝ) + 1)) (by positivity)
  choose first second small indices large using counterexamples
  have close : Tendsto (fun step => dist (first step) (second step)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun step => (small step).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have converges := sequential indices first second close
  have upper := converges.eventually (gt_mem_nhds positive)
  obtain ⟨step, bound⟩ := upper.exists
  exact (not_lt_of_ge (large step)) bound
