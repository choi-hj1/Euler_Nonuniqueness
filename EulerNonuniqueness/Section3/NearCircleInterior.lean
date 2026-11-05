import EulerNonuniqueness.Section3.PolarInterior

open Set Metric

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def nearCircleInterior (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) : Set ℂ :=
  polarInterior (nearCircleRadialProfile data small)

theorem nearCircleInterior_isOpen (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) : IsOpen (nearCircleInterior data small) :=
  polarInterior_isOpen _ (nearCircleRadialProfile_continuous data small)
    (nearCircleRadialProfile_periodic data small) (by linarith : 0 < 1 - ‖data - standardCircleBanach‖)
    (nearCircleRadialProfile_lower data small)

theorem nearCircleInterior_isBounded (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) : Bornology.IsBounded (nearCircleInterior data small) :=
  polarInterior_isBounded _ (nearCircleRadialProfile_upper data small)

theorem nearCircleInterior_contains_ball (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    Metric.ball (0 : ℂ) (1 - ‖data - standardCircleBanach‖) ⊆ nearCircleInterior data small :=
  polarInterior_contains_ball _ (nearCircleRadialProfile_lower data small)

theorem nearCircleInterior_subset_ball (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    nearCircleInterior data small ⊆ Metric.ball (0 : ℂ) (1 + ‖data - standardCircleBanach‖) := by
  intro position membership
  change dist position 0 < 1 + ‖data - standardCircleBanach‖
  rw [dist_zero_right]
  exact membership.trans_le (nearCircleRadialProfile_upper data small _)

theorem nearCircleInterior_frontier (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    frontier (nearCircleInterior data small) = Set.range data.val.1 := by
  rw [nearCircleInterior, polarInterior_frontier_range _ (nearCircleRadialProfile_continuous data small)
    (nearCircleRadialProfile_periodic data small) (by linarith : 0 < 1 - ‖data - standardCircleBanach‖)
    (nearCircleRadialProfile_lower data small)]
  ext position
  constructor
  · rintro ⟨angle, rfl⟩
    exact ⟨nearCircleInverseAngle data small angle, nearCircleRadialProfile_parametrizes data small angle⟩
  · rintro ⟨label, rfl⟩
    refine ⟨nearCircleAngularLift data label, ?_⟩
    dsimp only
    rw [← nearCircleRadialProfile_parametrizes, nearCircleInverseAngle_left]

theorem nearCircleInterior_zero_mem (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) : (0 : ℂ) ∈ nearCircleInterior data small :=
  nearCircleInterior_contains_ball data small (mem_ball_self (by linarith))

theorem nearCircleRadialProfile_standardCircle
    (small : ‖standardCircleBanach - standardCircleBanach‖ < 1 / 3) (angle : ℝ) :
    nearCircleRadialProfile standardCircleBanach small angle = 1 :=
  standardCircle_norm _

theorem nearCircleInterior_standardCircle
    (small : ‖standardCircleBanach - standardCircleBanach‖ < 1 / 3) :
    nearCircleInterior standardCircleBanach small = Metric.ball (0 : ℂ) 1 := by
  ext position
  change ‖position‖ < nearCircleRadialProfile standardCircleBanach small (Complex.arg position) ↔ dist position 0 < 1
  rw [nearCircleRadialProfile_standardCircle, dist_zero_right]

end

end EulerNonuniqueness.Paper
