import Mathlib

namespace EulerNonuniqueness.General

open Filter Set Metric
open scoped Topology

variable {Target : Type*} [TopologicalSpace Target]

theorem exists_continuousOn_interval_of_eventually_continuousAt
    (function : ℝ → Target)
    (nearby : ∀ᶠ parameter in 𝓝 (0 : ℝ), ContinuousAt function parameter) :
    ∃ radius > 0, ContinuousOn function (Icc (-radius) radius) := by
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp nearby
  refine ⟨radius / 2, by positivity, ?_⟩
  intro parameter member
  apply ContinuousAt.continuousWithinAt
  apply contained
  rw [mem_ball_zero_iff, Real.norm_eq_abs]
  exact (abs_le.mpr member).trans_lt (by linarith)

end EulerNonuniqueness.General
