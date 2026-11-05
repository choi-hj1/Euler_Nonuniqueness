import EulerNonuniqueness.Section3.DiskSpectralStationarySecond
import EulerNonuniqueness.General.StationarySecondLipschitz
import EulerNonuniqueness.General.LocalFiberOperatorBounds

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskSpectralTubularStationarySecond_lipschitzNear :
    EulerNonuniqueness.General.LipschitzNear diskSpectralTubularStationarySecond 0 := by
  have derivativeLip := diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.2
  unfold diskSpectralTubularStationarySecond
  with_reducible
    exact EulerNonuniqueness.General.spectralTubularStationarySecond_lipschitzNear
      diskRelabelNeutralCLM diskChartedSpectralCoordinates (0 : PeriodicC1HolderHalf)
      derivativeLip

theorem diskSpectralTubularStationarySecond_exists_uniform_bound :
    ∃ constant ≥ 0, ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskSpectralTubularStationarySecond point‖ ≤ constant := by
  with_reducible
    exact EulerNonuniqueness.General.exists_eventually_norm_bound
      (Space := PeriodicC1HolderHalf)
      (Target := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
      diskSpectralTubularStationarySecond_lipschitzNear.continuousAt

end EulerNonuniqueness.Paper
