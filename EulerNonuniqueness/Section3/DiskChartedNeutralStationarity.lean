import EulerNonuniqueness.Section3.DiskChartedNeutralJet
import EulerNonuniqueness.Section3.DiskRelabelNeutralPart

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance neutralStationarityContinuousNeg : ContinuousNeg PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousNeg
local instance neutralStationarityContinuousSub : ContinuousSub PeriodicC1HolderHalf :=
  ⟨by simpa only [sub_eq_add_neg] using
    (continuous_fst.add continuous_snd.neg :
      Continuous (fun pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf => pair.1 + -pair.2))⟩

theorem diskChartedEulerField_eventually_neutral_stationary :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      diskChartedEulerField (diskRelabelNeutralCLM increment) = 0 := by
  have convergence : Tendsto
      (fun increment : PeriodicC1HolderHalf =>
        ‖diskStationaryChart (diskRelabelNeutralCLM increment) - standardCircleBanach‖)
      (𝓝 0) (𝓝 (0 : ℝ)) := by
    have chart := (diskStationaryChart_analyticAt 0).continuousAt.tendsto
    have neutral := diskRelabelNeutralCLM.continuous.tendsto (0 : PeriodicC1HolderHalf)
    have composed := ((chart.comp (by simpa only [map_zero] using neutral)).sub
      (tendsto_const_nhds (x := standardCircleBanach))).norm
    simpa [Function.comp_def, diskStationaryChart_zero] using composed
  have small := convergence.eventually (eventually_lt_nhds
    (lt_min (by norm_num : (0 : ℝ) < 1 / 3) (by positivity : 0 < 2 / (3 * Real.pi))))
  filter_upwards [small] with increment close
  have chartIdentity : diskStationaryChart (diskRelabelNeutralCLM increment) =
      diskRelabelCurve (diskNeutralCLM increment) 1 := by
    rw [diskRelabelNeutralCLM_apply, diskStationaryChart_relabel _ (diskNeutralCLM_real increment)]
  rw [chartIdentity] at close
  have zero := diskEulerRotatingField_relabel_zero (diskNeutralCLM increment)
    (diskNeutralCLM_real increment) (close.trans_le (min_le_left _ _))
    (close.trans_le (min_le_right _ _))
  unfold diskChartedEulerField
  rw [chartIdentity, zero, map_zero]

end

end EulerNonuniqueness.Paper
