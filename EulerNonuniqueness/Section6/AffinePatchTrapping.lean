import EulerNonuniqueness.Section3.AffinePatchDomain

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem affinePatchDomain_contains_ball (center : ℂ) {radius : ℝ} (radiusPositive : 0 < radius)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    Metric.ball center (radius * (1 - ‖data - standardCircleBanach‖)) ⊆
      affinePatchDomain center radius data small := by
  intro position member
  have bound : ‖position - center‖ < radius * (1 - ‖data - standardCircleBanach‖) := by
    simpa [Metric.mem_ball, dist_eq_norm] using member
  refine ⟨radius⁻¹ • (position - center), nearCircleInterior_contains_ball data small ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr radiusPositive)]
    calc
      _ < radius⁻¹ * (radius * (1 - ‖data - standardCircleBanach‖)) :=
        mul_lt_mul_of_pos_left bound (inv_pos.mpr radiusPositive)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ radiusPositive.ne', one_mul]
  · dsimp only
    rw [smul_smul, mul_inv_cancel₀ radiusPositive.ne', one_smul]
    abel

theorem affinePatchDomain_subset_ball (center : ℂ) {radius : ℝ} (radiusPositive : 0 < radius)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    affinePatchDomain center radius data small ⊆
      Metric.ball center (radius * (1 + ‖data - standardCircleBanach‖)) := by
  rintro position ⟨normalized, member, rfl⟩
  have bound := nearCircleInterior_subset_ball data small member
  have normalizedBound : ‖normalized‖ < 1 + ‖data - standardCircleBanach‖ := by simpa using bound
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos radiusPositive]
  exact mul_lt_mul_of_pos_left normalizedBound radiusPositive

end EulerNonuniqueness.Paper
