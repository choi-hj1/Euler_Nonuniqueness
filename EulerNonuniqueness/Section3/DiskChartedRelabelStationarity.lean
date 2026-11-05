import EulerNonuniqueness.Section3.DiskChartedRelabelPeriodFamily

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance chartedStationarityHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance chartedStationarityC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem diskChartedEulerField_relabel_eventually_zero
    (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    ∀ᶠ scalar in 𝓝 (0 : ℝ),
      diskChartedEulerField (scalar • diskMaterialPerturbation 0 angular) = 0 := by
  filter_upwards [diskRelabelCurve_eventually_stationary angular realValues] with scalar stationary
  have realScaled (label : ℝ) : star ((scalar • angular).val.1 label) = (scalar • angular).val.1 label := by
    change star (scalar • angular.val.1 label) = scalar • angular.val.1 label
    rw [star_smul, star_trivial, realValues]
  have chartIdentity : diskStationaryChart (scalar • diskMaterialPerturbation 0 angular) =
      diskRelabelCurve angular scalar := by
    rw [← diskMaterialPerturbation_zero_real_smul, diskStationaryChart_relabel _ realScaled,
      diskRelabelCurve_real_smul]
  have fieldZero : diskEulerRotatingField (diskRelabelCurve angular scalar) = 0 := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    have actual := congrArg (fun value : PeriodicC1HolderHalf => value.val.1 label) stationary
    exact actual
  unfold diskChartedEulerField
  rw [chartIdentity, fieldZero, map_zero]

end

end EulerNonuniqueness.Paper
