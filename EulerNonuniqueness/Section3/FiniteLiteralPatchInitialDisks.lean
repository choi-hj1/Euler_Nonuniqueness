import EulerNonuniqueness.Section3.FiniteLiteralPatchArea

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem affinePatchDomain_standardCircle (center : ℂ) {radius : ℝ} (positive : 0 < radius)
    (small : ‖standardCircleBanach - standardCircleBanach‖ < 1 / 3) :
    affinePatchDomain center radius standardCircleBanach small = Metric.ball center radius := by
  unfold affinePatchDomain
  rw [nearCircleInterior_standardCircle small]
  ext position
  constructor
  · rintro ⟨normalized, member, rfl⟩
    have bound : ‖normalized‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using member
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos positive]
    nlinarith
  · intro member
    have bound : ‖position - center‖ < radius := by simpa only [Metric.mem_ball, dist_eq_norm] using member
    refine ⟨radius⁻¹ • (position - center), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive)]
      exact (inv_mul_lt_one₀ positive).mpr bound
    · dsimp only
      rw [smul_smul, mul_inv_cancel₀ positive.ne', one_smul]
      exact add_sub_cancel _ _

theorem FiniteLiteralPatchFlow.domain_initial_eq_ball {count : ℕ}
    {configuration : FiniteContourConfiguration count} (flow : FiniteLiteralPatchFlow configuration) (index : Fin count) :
    flow.domain 0 index = Metric.ball (configuration.center index) (configuration.radius index) := by
  have initial_component : flow.shape 0 index = standardCircleBanach := congrFun flow.initial index
  have small : ‖standardCircleBanach - standardCircleBanach‖ < 1 / 3 := by norm_num
  calc
    _ = affinePatchDomain (configuration.center index) (configuration.radius index) standardCircleBanach small :=
      affinePatchDomain_congr _ _ initial_component _ small
    _ = _ := affinePatchDomain_standardCircle _ (configuration.radius_pos index) small

end

end EulerNonuniqueness.Paper
