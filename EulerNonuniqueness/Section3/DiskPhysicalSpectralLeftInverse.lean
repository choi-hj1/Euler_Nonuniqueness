import EulerNonuniqueness.Section3.DiskPhysicalSpectralStationaryJet

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance physicalSpectralLeftInverseC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskPhysicalSpectralCoordinate_eventually_left_inverse :
    ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf),
      diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart point) = point := by
  have tubularLimit : Tendsto diskSpectralTubularChart (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 0) := by
    simpa only [diskSpectralTubularChart_zero] using
      diskSpectralTubularChart_hasLipschitzDerivativeNear.lipschitzNear.continuousAt.tendsto
  have stationarySource := tubularLimit.eventually (diskStationaryChartPartialHomeomorph.open_source.mem_nhds
    diskStationaryChart_zero_mem_source)
  filter_upwards [stationarySource, diskSpectralTubularPartialHomeomorph.open_source.mem_nhds
    diskSpectralTubularPartialHomeomorph_zero_mem_source] with point stationaryInside tubularInside
  have firstInverse : diskStationaryChartPartialHomeomorph.symm
      (diskStationaryChart (diskSpectralTubularChart point)) = diskSpectralTubularChart point :=
    diskStationaryChartPartialHomeomorph.left_inv stationaryInside
  unfold diskPhysicalSpectralCoordinate diskPhysicalSpectralChart
  rw [firstInverse]
  exact diskSpectralTubularPartialHomeomorph.left_inv tubularInside

end EulerNonuniqueness.Paper
