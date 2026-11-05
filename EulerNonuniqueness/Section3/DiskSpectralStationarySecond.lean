import EulerNonuniqueness.Section3.DiskSpectralTubularChart
import EulerNonuniqueness.General.SpectralTubularStationarySecond
import EulerNonuniqueness.General.LocalRegularityNeighborhood

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance stationarySpectralSecondC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

def diskSpectralTubularStationarySecond (point : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.spectralTubularStationarySecond
    diskRelabelNeutralCLM diskChartedSpectralCoordinates point

theorem diskSpectralTubularChart_eventually_stationary_second :
    ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf), diskRelabelNeutralCLM point = point →
      HasFDerivAt (fderiv ℝ diskSpectralTubularChart) (diskSpectralTubularStationarySecond point) point ∧
        ∀ first second, diskSpectralTubularStationarySecond point first second =
          diskSpectralTubularStationarySecond point second first := by
  have fixes : ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf),
      (diskChartedSpectralCoordinates point).comp diskRelabelNeutralCLM = diskRelabelNeutralCLM := by
    filter_upwards [diskChartedSpectralCoordinates_eventually_fixes_relabel] with point actual
    apply ContinuousLinearMap.ext
    intro direction
    exact actual direction
  filter_upwards [diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.eventually, fixes.eventually_nhds]
    with point regular pointFixes neutral
  obtain ⟨differentiable, derivativeLip⟩ := regular
  have derivativeContinuous := derivativeLip.continuousAt
  unfold diskSpectralTubularChart diskSpectralTubularStationarySecond
  constructor
  · with_reducible
      exact EulerNonuniqueness.General.spectralTubularChart_hasFDerivAt_fderiv_stationary
        diskRelabelNeutralCLM diskChartedSpectralCoordinates point neutral differentiable derivativeContinuous pointFixes
  · intro first second
    with_reducible
      exact EulerNonuniqueness.General.spectralTubularStationarySecond_symmetric
        diskRelabelNeutralCLM diskChartedSpectralCoordinates point neutral differentiable derivativeContinuous
        pointFixes first second

end EulerNonuniqueness.Paper
