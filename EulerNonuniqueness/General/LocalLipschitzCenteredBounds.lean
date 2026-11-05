import EulerNonuniqueness.Section3.LocalLipschitzCalculus

noncomputable section

open Set Metric
open scoped Topology

namespace EulerNonuniqueness.General

variable {Domain Target : Type*} [NormedAddCommGroup Domain] [NormedAddCommGroup Target]

theorem LipschitzNear.exists_centered_closedBall_difference_bound
    {function : Domain → Target} {center : Domain} (regular : LipschitzNear function center) :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ first second : Domain, ‖first - center‖ ≤ radius → ‖second - center‖ ≤ radius →
        ‖function first - function second‖ ≤ constant * ‖first - second‖ := by
  obtain ⟨lipschitzConstant, neighborhood, nearby, lipschitz⟩ := regular
  obtain ⟨outerRadius, positive, contained⟩ := Metric.mem_nhds_iff.mp nearby
  have inside (data : Domain) (small : ‖data - center‖ ≤ outerRadius / 2) : data ∈ neighborhood := by
    apply contained
    rw [Metric.mem_ball, dist_eq_norm]
    exact small.trans_lt (by linarith)
  refine ⟨outerRadius / 2, by positivity, (lipschitzConstant : ℝ) + 1, by linarith [lipschitzConstant.coe_nonneg], ?_⟩
  intro first second firstSmall secondSmall
  exact (lipschitz.norm_sub_le (inside first firstSmall) (inside second secondSmall)).trans
    (mul_le_mul_of_nonneg_right (by linarith : (lipschitzConstant : ℝ) ≤ lipschitzConstant + 1) (norm_nonneg _))

end EulerNonuniqueness.General
