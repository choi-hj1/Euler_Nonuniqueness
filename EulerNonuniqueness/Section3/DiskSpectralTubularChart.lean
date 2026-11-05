import EulerNonuniqueness.Section3.DiskChartedStationarySubspace
import EulerNonuniqueness.General.SpectralTubularChart

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

def diskSpectralTubularChart : PeriodicC1HolderHalf → PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.spectralTubularChart (Space := PeriodicC1HolderHalf)
    diskRelabelNeutralCLM diskChartedSpectralCoordinates

theorem diskSpectralTubularChart_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear diskSpectralTubularChart 0 := by
  unfold diskSpectralTubularChart
  with_reducible
    exact EulerNonuniqueness.General.spectralTubularChart_hasLipschitzDerivativeNear
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskChartedSpectralCoordinates
      diskChartedSpectralCoordinates_hasLipschitzDerivativeNear

theorem diskSpectralTubularChart_hasStrictFDerivAt_zero :
    HasStrictFDerivAt diskSpectralTubularChart (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf) 0 := by
  unfold diskSpectralTubularChart
  with_reducible
    exact EulerNonuniqueness.General.spectralTubularChart_hasStrictFDerivAt_zero
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskChartedSpectralCoordinates
      diskChartedSpectralCoordinates_hasLipschitzDerivativeNear diskChartedSpectralCoordinates_zero

theorem diskSpectralTubularChart_zero : diskSpectralTubularChart 0 = 0 := by
  unfold diskSpectralTubularChart
  with_reducible
    exact EulerNonuniqueness.General.spectralTubularChart_zero (Space := PeriodicC1HolderHalf)
      diskRelabelNeutralCLM diskChartedSpectralCoordinates

theorem diskSpectralTubularChart_stationary (increment : PeriodicC1HolderHalf) :
    diskSpectralTubularChart (diskRelabelNeutralCLM increment) = diskRelabelNeutralCLM increment := by
  unfold diskSpectralTubularChart
  have idempotent := diskRelabelNeutralCLM_idempotent increment
  with_reducible
    exact EulerNonuniqueness.General.spectralTubularChart_stationary (Space := PeriodicC1HolderHalf)
      diskRelabelNeutralCLM diskChartedSpectralCoordinates increment idempotent

theorem diskSpectralTubularChart_eventually_stationary_derivative :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      HasFDerivAt diskSpectralTubularChart (diskChartedSpectralCoordinates increment) (diskRelabelNeutralCLM increment) := by
  have neutralLimit : Tendsto diskRelabelNeutralCLM (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 0) := by
    simpa only [map_zero] using diskRelabelNeutralCLM.continuous.tendsto (0 : PeriodicC1HolderHalf)
  filter_upwards [neutralLimit.eventually diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.1,
    neutralLimit.eventually diskChartedSpectralCoordinates_eventually_fixes_relabel] with increment regular fixed
  have fixes : (diskChartedSpectralCoordinates (diskRelabelNeutralCLM increment)).comp diskRelabelNeutralCLM =
      diskRelabelNeutralCLM := by
    apply ContinuousLinearMap.ext
    intro direction
    exact fixed direction
  have actual : HasFDerivAt diskSpectralTubularChart
      (diskChartedSpectralCoordinates (diskRelabelNeutralCLM increment)) (diskRelabelNeutralCLM increment) := by
    unfold diskSpectralTubularChart
    with_reducible
      exact EulerNonuniqueness.General.spectralTubularChart_hasFDerivAt_stationary_of_differentiable
        (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskChartedSpectralCoordinates increment
        regular (diskRelabelNeutralCLM_idempotent increment) fixes
  rwa [diskChartedSpectralCoordinates_neutral_parameter] at actual

end

end EulerNonuniqueness.Paper
