import EulerNonuniqueness.Section3.DiskStationaryAreaFactor
import EulerNonuniqueness.Section3.DiskRelabelNeutralPart

namespace EulerNonuniqueness.Paper

noncomputable section

open Set Metric Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance uniformAreaFactorHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance uniformAreaFactorC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem diskStationaryArea_exists_uniform_factored_mean_bound :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ angular : PeriodicC1HolderHalf,
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ transverse : PeriodicC1HolderHalf,
      ‖diskMaterialPerturbation 0 angular‖ + ‖transverse‖ ≤ radius →
      diskStationaryArea (diskMaterialPerturbation 0 angular + transverse) = Real.pi →
      |diskRadialMean (diskMaterialPerturbation 0 angular + transverse)| ≤
        constant * (‖diskMaterialPerturbation 0 angular‖ + ‖transverse‖) * ‖transverse‖ := by
  obtain ⟨radius, positive, constant, nonnegative, estimate⟩ := diskStationaryArea_exists_factored_mean_bound
  have chartContinuous : ContinuousAt diskStationaryChart (0 : PeriodicC1HolderHalf) :=
    HasStrictFDerivAt.continuousAt (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      diskStationaryChart_hasStrictFDerivAt_zero
  have normConvergence : Tendsto (fun value : PeriodicC1HolderHalf => ‖diskStationaryChart value - standardCircleBanach‖)
      (𝓝 0) (𝓝 (0 : ℝ)) := by
    have actual := chartContinuous.tendsto.dist (tendsto_const_nhds (x := standardCircleBanach))
    have distance (value : PeriodicC1HolderHalf) : dist value standardCircleBanach = ‖value - standardCircleBanach‖ :=
      dist_eq_norm value standardCircleBanach
    simpa only [diskStationaryChart_zero, dist_self, distance] using actual
  have nearby : {value : PeriodicC1HolderHalf | ‖diskStationaryChart value - standardCircleBanach‖ < 1 / 3} ∈
      𝓝 (0 : PeriodicC1HolderHalf) :=
    normConvergence.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 3))
  obtain ⟨margin, marginPositive, contained⟩ := Metric.mem_nhds_iff.mp nearby
  refine ⟨min radius (margin / 2), lt_min positive (by positivity), constant, nonnegative, ?_⟩
  intro angular realValues transverse inside area
  have labelSmall : ‖diskMaterialPerturbation 0 angular‖ < margin := by
    have normSmall := (le_add_of_nonneg_right (norm_nonneg transverse)).trans inside
    exact (normSmall.trans (min_le_right _ _)).trans_lt (by linarith)
  have chartSmall := contained (show diskMaterialPerturbation 0 angular ∈ ball (0 : PeriodicC1HolderHalf) margin by
    with_reducible
      exact (mem_ball_zero_iff (E := PeriodicC1HolderHalf)).mpr labelSmall)
  change ‖diskStationaryChart (diskMaterialPerturbation 0 angular) - standardCircleBanach‖ < 1 / 3 at chartSmall
  rw [diskStationaryChart_relabel angular realValues] at chartSmall
  exact estimate angular realValues transverse (inside.trans (min_le_left _ _)) chartSmall area

theorem diskStationaryArea_exists_relabel_factored_mean_bound :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ increment : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖ ≤ radius →
      diskStationaryArea increment = Real.pi →
      |diskRadialMean increment| ≤ constant *
        (‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖) *
        ‖increment - diskRelabelNeutralCLM increment‖ := by
  obtain ⟨radius, positive, constant, nonnegative, estimate⟩ := diskStationaryArea_exists_uniform_factored_mean_bound
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  intro increment inside area
  have reconstruction : diskRelabelNeutralCLM increment + (increment - diskRelabelNeutralCLM increment) = increment := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (diskRelabelNeutralCLM increment).val.1 label +
      (increment.val.1 label - (diskRelabelNeutralCLM increment).val.1 label) = increment.val.1 label
    ring
  have actual := estimate (diskNeutralCLM increment) (diskNeutralCLM_real increment)
    (increment - diskRelabelNeutralCLM increment)
  rw [← diskRelabelNeutralCLM_apply, reconstruction] at actual
  exact actual inside area

end

end EulerNonuniqueness.Paper
