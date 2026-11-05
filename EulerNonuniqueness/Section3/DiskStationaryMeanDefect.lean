import EulerNonuniqueness.Section3.DiskStationaryAreaAbsorption

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance stationaryMeanDefectHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance stationaryMeanDefectC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem diskStationaryArea_exists_projected_mean_defect_bound :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ increment : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖ ≤ radius →
      diskStationaryArea increment = Real.pi →
      ‖increment - diskRelabelNeutralCLM increment - diskPhysicalTransverseProjection increment‖ ≤
        constant * (‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖) *
          ‖diskPhysicalTransverseProjection increment‖ := by
  obtain ⟨factorRadius, factorPositive, constant, nonnegative, factorEstimate⟩ :=
    diskStationaryArea_exists_relabel_factored_mean_bound
  obtain ⟨absorptionRadius, absorptionPositive, absorptionEstimate⟩ :=
    diskStationaryArea_exists_transverse_norm_absorption
  refine ⟨min factorRadius absorptionRadius, lt_min factorPositive absorptionPositive,
    16 * ‖standardCircleBanach‖ * constant, by positivity, ?_⟩
  intro increment inside area
  have mean := factorEstimate increment (inside.trans (min_le_left _ _)) area
  have relative := absorptionEstimate increment (inside.trans (min_le_right _ _)) area
  have meanIdentity : increment - diskRelabelNeutralCLM increment - diskPhysicalTransverseProjection increment =
      c1Product standardCircleBanach (c1Constant (diskRadialMean increment : ℂ)) := by
    rw [diskPhysical_relabel_neutral_decomposition]
    with_reducible abel
  rw [meanIdentity]
  calc
    _ ≤ (8 * ‖standardCircleBanach‖) * |diskRadialMean increment| :=
      norm_diskAreaMeanComponent_le (diskRadialMean increment)
    _ ≤ (8 * ‖standardCircleBanach‖) *
        (constant * (‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖) *
          ‖increment - diskRelabelNeutralCLM increment‖) :=
      mul_le_mul_of_nonneg_left mean (by positivity)
    _ ≤ (8 * ‖standardCircleBanach‖) *
        (constant * (‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖) *
          (2 * ‖diskPhysicalTransverseProjection increment‖)) := by gcongr
    _ = _ := by ring

end

end EulerNonuniqueness.Paper
