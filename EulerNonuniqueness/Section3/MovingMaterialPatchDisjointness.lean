import EulerNonuniqueness.Section3.MovingMaterialPatch

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

theorem domain_subset_center_ball (path : MovingMaterialPatch) (time : ℝ) :
    path.domain time ⊆ ball (path.center time) (2 * path.radius) := by
  rintro position ⟨normalized, member, rfl⟩
  have bound := nearCircleInterior_subset_ball (path.shape time) (path.nearby time) member
  have normalizedBound : ‖normalized‖ < 1 + ‖path.shape time - standardCircleBanach‖ := by
    simpa only [mem_ball, dist_zero_right] using bound
  have normalizedSmall : ‖normalized‖ < 2 := by linarith [path.nearby time]
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos path.radius_positive, norm_mul, Circle.norm_coe, one_mul]
  simpa only [mul_comm path.radius 2] using mul_lt_mul_of_pos_left normalizedSmall path.radius_positive

theorem domains_disjoint_of_center_distance (first second : MovingMaterialPatch) (time : ℝ)
    (separated : 2 * first.radius + 2 * second.radius ≤ dist (first.center time) (second.center time)) :
    Disjoint (first.domain time) (second.domain time) := by
  apply Set.disjoint_left.mpr
  intro position firstInside secondInside
  have firstBound := first.domain_subset_center_ball time firstInside
  have secondBound := second.domain_subset_center_ball time secondInside
  rw [mem_ball] at firstBound secondBound
  have triangle := dist_triangle (first.center time) position (second.center time)
  rw [dist_comm (first.center time) position] at triangle
  linarith

end EulerNonuniqueness.Paper.MovingMaterialPatch
