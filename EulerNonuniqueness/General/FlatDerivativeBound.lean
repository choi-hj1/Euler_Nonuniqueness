import Mathlib

namespace EulerNonuniqueness.General

noncomputable section

open Set Metric
open scoped Topology

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem exists_local_derivative_linear_bound_of_contDiff_two
    (function : Domain → Range) (smooth : ContDiff ℝ 2 function)
    (flat : fderiv ℝ function (0 : Domain) = 0) :
    ∃ radius > 0, ∃ constant ≥ 0,
      (∀ value ∈ closedBall (0 : Domain) radius, HasFDerivAt function (fderiv ℝ function value) value) ∧
      ∀ value ∈ closedBall (0 : Domain) radius, ‖fderiv ℝ function value‖ ≤ constant * ‖value‖ := by
  have derivativeSmooth : ContDiff ℝ 1 (fderiv ℝ function) := smooth.fderiv_right (by norm_num)
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ := derivativeSmooth.contDiffAt.exists_lipschitzOnWith
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp nearby
  have subset : closedBall (0 : Domain) (radius / 2) ⊆ neighborhood := by
    intro value member
    apply contained
    rw [mem_ball_zero_iff]
    exact (mem_closedBall_zero_iff.mp member).trans_lt (by linarith)
  refine ⟨radius / 2, by positivity, (constant : ℝ), constant.coe_nonneg, ?_, ?_⟩
  · intro value _member
    exact (smooth.differentiable (by norm_num) value).hasFDerivAt
  · intro value member
    have zeroMember : (0 : Domain) ∈ neighborhood := mem_of_mem_nhds nearby
    have actual := lipschitz.norm_sub_le (subset member) zeroMember
    simpa only [flat, sub_zero] using actual

end

end EulerNonuniqueness.General
