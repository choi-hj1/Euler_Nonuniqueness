import EulerNonuniqueness.Section6.AffinePatchTrapping

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem nearCircleRadialProfile_abs_sub_one_le (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) {error : ℝ}
    (radialBound : ∀ label : ℝ, |‖data.val.1 label‖ - 1| ≤ error) (angle : ℝ) :
    |nearCircleRadialProfile data small angle - 1| ≤ error :=
  radialBound (nearCircleInverseAngle data small angle)

theorem nearCircleInterior_radial_trapping (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) {error : ℝ}
    (radialBound : ∀ label : ℝ, |‖data.val.1 label‖ - 1| ≤ error) :
    Metric.ball (0 : ℂ) (1 - error) ⊆ nearCircleInterior data small ∧
      nearCircleInterior data small ⊆ Metric.ball (0 : ℂ) (1 + error) := by
  have profileBound := fun angle => abs_le.mp (nearCircleRadialProfile_abs_sub_one_le data small radialBound angle)
  constructor
  · apply polarInterior_contains_ball
    intro angle
    linarith [(profileBound angle).1]
  · intro position member
    change ‖position‖ < nearCircleRadialProfile data small (Complex.arg position) at member
    rw [Metric.mem_ball, dist_zero_right]
    exact member.trans_le (by linarith [(profileBound (Complex.arg position)).2])

theorem affinePatchDomain_radial_trapping (center : ℂ) {radius : ℝ}
    (radiusPositive : 0 < radius) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) {error : ℝ}
    (radialBound : ∀ label : ℝ, |‖data.val.1 label‖ - 1| ≤ error) :
    Metric.ball center (radius * (1 - error)) ⊆ affinePatchDomain center radius data small ∧
      affinePatchDomain center radius data small ⊆ Metric.ball center (radius * (1 + error)) := by
  have trapping := nearCircleInterior_radial_trapping data small radialBound
  constructor
  · intro position member
    have bound : ‖position - center‖ < radius * (1 - error) := by
      simpa only [Metric.mem_ball, dist_eq_norm] using member
    refine ⟨radius⁻¹ • (position - center), trapping.1 ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr radiusPositive)]
      calc
        _ < radius⁻¹ * (radius * (1 - error)) :=
          mul_lt_mul_of_pos_left bound (inv_pos.mpr radiusPositive)
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ radiusPositive.ne', one_mul]
    · dsimp only
      rw [smul_smul, mul_inv_cancel₀ radiusPositive.ne', one_smul]
      abel
  · rintro position ⟨normalized, member, rfl⟩
    have bound := trapping.2 member
    have normalizedBound : ‖normalized‖ < 1 + error := by simpa only [Metric.mem_ball, dist_zero_right] using bound
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos radiusPositive]
    exact mul_lt_mul_of_pos_left normalizedBound radiusPositive

end EulerNonuniqueness.Paper
