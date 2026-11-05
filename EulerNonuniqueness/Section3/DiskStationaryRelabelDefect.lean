import EulerNonuniqueness.Section3.DiskStationaryAreaAbsorption
import EulerNonuniqueness.General.ExponentialStationaryMultiplier

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance stationaryRelabelDefectHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance stationaryRelabelDefectC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem diskStationaryChartGenerator_eq_relabel (increment : PeriodicC1HolderHalf) :
    diskStationaryChartGenerator increment = diskRelabelGenerator (diskNeutralCLM increment) := by
  apply ContinuousLinearMap.ext
  intro value
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem diskStationaryChartGenerator_circle (increment : PeriodicC1HolderHalf) :
    diskStationaryChartGenerator increment standardCircleBanach = diskRelabelNeutralCLM increment := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (Complex.I * (diskNeutralCLM increment).val.1 label) * standardCircle label =
    standardCircle label * (Complex.I * (diskNeutralCLM increment).val.1 label)
  ring

theorem diskStationaryMultiplier_circle (increment : PeriodicC1HolderHalf) :
    EulerNonuniqueness.General.exponentialStationaryMultiplier (Space := PeriodicC1HolderHalf)
      diskStationaryChartGenerator increment standardCircleBanach =
      diskRelabelCurve (diskNeutralCLM increment) 1 := by
  have actual : EulerNonuniqueness.General.exponentialStationaryMultiplier (Space := PeriodicC1HolderHalf)
      diskStationaryChartGenerator increment standardCircleBanach =
      EulerNonuniqueness.General.linearExponentialCurve (Space := PeriodicC1HolderHalf)
        (diskStationaryChartGenerator increment) standardCircleBanach 1 := by
    with_reducible
      exact EulerNonuniqueness.General.exponentialStationaryMultiplier_apply_eq_curve
        (Space := PeriodicC1HolderHalf) diskStationaryChartGenerator increment standardCircleBanach
  rw [diskStationaryChartGenerator_eq_relabel] at actual
  exact actual

theorem diskStationaryChart_exists_relabel_defect_bound :
    ∃ radius > 0, ∀ increment : PeriodicC1HolderHalf, ‖increment‖ ≤ radius →
      ‖diskStationaryChart increment - diskRelabelCurve (diskNeutralCLM increment) 1‖ ≤
        2 * ‖increment - diskRelabelNeutralCLM increment‖ := by
  have actual : ∃ radius > 0, ∀ increment : PeriodicC1HolderHalf, ‖increment‖ ≤ radius →
      ‖EulerNonuniqueness.General.exponentialStationaryChart (Space := PeriodicC1HolderHalf)
          diskStationaryChartGenerator standardCircleBanach increment -
        EulerNonuniqueness.General.exponentialStationaryMultiplier (Space := PeriodicC1HolderHalf)
          diskStationaryChartGenerator increment standardCircleBanach‖ ≤
        2 * ‖increment - diskStationaryChartGenerator increment standardCircleBanach‖ := by
    with_reducible
      exact EulerNonuniqueness.General.exponentialStationaryChart_exists_relabel_defect_bound
        (Space := PeriodicC1HolderHalf) diskStationaryChartGenerator standardCircleBanach
  obtain ⟨radius, positive, estimate⟩ := actual
  refine ⟨radius, positive, ?_⟩
  intro increment inside
  have bound := estimate increment inside
  change ‖diskStationaryChart increment - _‖ ≤ _ at bound
  rw [diskStationaryMultiplier_circle, diskStationaryChartGenerator_circle] at bound
  exact bound

theorem diskStationaryArea_exists_projected_relabel_defect_bound :
    ∃ radius > 0, ∀ increment : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖ ≤ radius →
      diskStationaryArea increment = Real.pi →
      ‖diskStationaryChart increment - diskRelabelCurve (diskNeutralCLM increment) 1‖ ≤
        4 * ‖diskPhysicalTransverseProjection increment‖ := by
  obtain ⟨areaRadius, areaPositive, areaEstimate⟩ := diskStationaryArea_exists_transverse_norm_absorption
  obtain ⟨multiplierRadius, multiplierPositive, multiplierEstimate⟩ := diskStationaryChart_exists_relabel_defect_bound
  refine ⟨min areaRadius multiplierRadius, lt_min areaPositive multiplierPositive, ?_⟩
  intro increment inside area
  have reconstruction : diskRelabelNeutralCLM increment + (increment - diskRelabelNeutralCLM increment) = increment := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (diskRelabelNeutralCLM increment).val.1 label +
      (increment.val.1 label - (diskRelabelNeutralCLM increment).val.1 label) = increment.val.1 label
    ring
  have incrementNorm : ‖increment‖ ≤ ‖diskRelabelNeutralCLM increment‖ +
      ‖increment - diskRelabelNeutralCLM increment‖ := by
    nth_rw 1 [← reconstruction]
    with_reducible
      exact norm_add_le (diskRelabelNeutralCLM increment)
        (increment - diskRelabelNeutralCLM increment)
  exact (multiplierEstimate increment (incrementNorm.trans (inside.trans (min_le_right _ _)))).trans
    ((mul_le_mul_of_nonneg_left (areaEstimate increment (inside.trans (min_le_left _ _)) area)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

end

end EulerNonuniqueness.Paper
