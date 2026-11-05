import EulerNonuniqueness.Section3.DiskPhysicalSpectralRelativeArea
import EulerNonuniqueness.General.LocalLipschitzBallBounds

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance affineDefectBoundsC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskPhysicalSpectralDefect_exists_transverse_bound :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ state : PeriodicC1HolderHalf,
      state ∈ ball 0 radius → diskSpectralTubularArea state = Real.pi →
      ‖diskPhysicalSpectralDefect state‖ ≤ constant * ‖diskPhysicalTransverseProjection state‖ := by
  obtain ⟨radius, positive, constant, nonnegative, difference⟩ :=
    diskPhysicalSpectralDefect_exists_relative_physical_ball
  have areaZero : diskSpectralTubularArea (0 : PeriodicC1HolderHalf) = Real.pi := by
    rw [diskSpectralTubularArea, diskSpectralTubularChart_zero, diskStationaryArea_zero]
  have defectZero : diskPhysicalSpectralDefect (0 : PeriodicC1HolderHalf) = 0 := by
    rw [diskPhysicalSpectralDefect, diskPhysicalSpectralChart_zero, map_zero, diskStationaryChart_zero, sub_self]
  refine ⟨min radius 1, lt_min positive (by norm_num),
    constant * (1 + ‖diskRelabelNeutralCLM‖), by positivity, ?_⟩
  intro state inside area
  have normInside : ‖state‖ < min radius 1 := by simpa only [mem_ball, dist_zero_right] using inside
  have stateInside : state ∈ ball 0 radius := by
    simpa only [mem_ball, dist_zero_right] using normInside.trans_le (min_le_left radius 1)
  have neutralBound : ‖diskRelabelNeutralCLM state‖ ≤ ‖diskRelabelNeutralCLM‖ :=
    (diskRelabelNeutralCLM.le_opNorm state).trans
      (mul_le_of_le_one_right (norm_nonneg _) (normInside.trans_le (min_le_right radius 1)).le)
  have estimate := difference state 0 stateInside (by simpa only [mem_ball, dist_self] using positive) area areaZero
  simp only [defectZero, map_zero, sub_zero, norm_zero, add_zero] at estimate
  apply estimate.trans
  nlinarith [mul_nonneg nonnegative (mul_nonneg (norm_nonneg (diskPhysicalTransverseProjection state))
    (sub_nonneg.mpr neutralBound))]

theorem diskStationaryChart_exists_neutral_base_difference_bound :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM initial‖ ≤ radius → ‖diskRelabelNeutralCLM final‖ ≤ radius →
      ‖diskStationaryChart (diskRelabelNeutralCLM initial) -
          diskStationaryChart (diskRelabelNeutralCLM final)‖ ≤
        constant * ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖ := by
  have regular : EulerNonuniqueness.General.HasLipschitzDerivativeNear diskStationaryChart
      (0 : PeriodicC1HolderHalf) := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt (diskStationaryChart_analyticAt 0)
  obtain ⟨radius, positive, constant, one, _, difference⟩ :=
    EulerNonuniqueness.General.LipschitzNear.exists_closedBall_bounds regular.lipschitzNear
  refine ⟨radius, positive, constant, le_trans (by norm_num) one, ?_⟩
  intro initial final initialInside finalInside
  exact difference _ _ initialInside finalInside

end EulerNonuniqueness.Paper
