import EulerNonuniqueness.Section3.DiskSpectralAreaRelativeRemainder
import EulerNonuniqueness.Section3.DiskSpectralAreaAbsorption

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd chartedBilinearGroup chartedBilinearModule
  stationaryAreaHolderSpace stationaryAreaC1Space
  stationaryAreaRemainderOperatorGroup stationaryAreaRemainderOperatorSpace

theorem diskSpectralAreaFiberRemainder_neutral_parameter (parameter increment : PeriodicC1HolderHalf) :
    diskSpectralAreaFiberRemainder (diskRelabelNeutralCLM parameter) increment =
      diskSpectralAreaFiberRemainder parameter increment := by
  unfold diskSpectralAreaFiberRemainder
  rw [diskRelabelNeutralCLM_idempotent, diskChartedSpectralCoordinates_neutral_parameter]

theorem diskSpectralTubularArea_eventually_linear_fiber_identity :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf), ∀ direction : PeriodicC1HolderHalf,
      fderiv ℝ diskSpectralTubularArea (diskRelabelNeutralCLM increment) direction =
        fderiv ℝ diskStationaryArea (diskRelabelNeutralCLM increment)
          (diskChartedSpectralCoordinates increment direction) := by
  filter_upwards [diskSpectralTubularChart_eventually_stationary_derivative]
    with increment chartDerivative direction
  have analytic := diskStationaryArea_analyticAt (diskRelabelNeutralCLM increment)
  have outer := analytic.differentiableAt.hasFDerivAt
  have atChart : HasFDerivAt diskStationaryArea
      (fderiv ℝ diskStationaryArea (diskRelabelNeutralCLM increment))
      (diskSpectralTubularChart (diskRelabelNeutralCLM increment)) := by
    rw [diskSpectralTubularChart_stationary]
    exact outer
  have composition := atChart.comp (diskRelabelNeutralCLM increment) chartDerivative
  have actual := composition.fderiv
  exact congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] ℝ => linear direction) actual

theorem diskSpectralTubularArea_eventually_fiber_mean_identity :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      diskSpectralTubularArea increment - Real.pi =
        diskSpectralAreaRadialCoefficient increment * diskRadialMean (increment - diskRelabelNeutralCLM increment) +
          diskSpectralAreaFiberRemainder (diskRelabelNeutralCLM increment)
            (increment - diskRelabelNeutralCLM increment) := by
  filter_upwards [diskSpectralTubularArea_eventually_linear_fiber_identity,
    diskSpectralTubularArea_eventually_stationary_transverse_derivative_zero,
    diskSpectralTubularArea_eventually_neutral_value] with increment derivative annihilates stationary
  let relative := increment - diskRelabelNeutralCLM increment
  have kernel : diskRelabelNeutralCLM relative = 0 := by
    have linearity : diskRelabelNeutralCLM (increment - diskRelabelNeutralCLM increment) =
        diskRelabelNeutralCLM increment - diskRelabelNeutralCLM (diskRelabelNeutralCLM increment) := by
      with_reducible exact map_sub diskRelabelNeutralCLM increment (diskRelabelNeutralCLM increment)
    change diskRelabelNeutralCLM (increment - diskRelabelNeutralCLM increment) = 0
    rw [linearity, diskRelabelNeutralCLM_idempotent]
    with_reducible exact sub_self (diskRelabelNeutralCLM increment)
  have decomposition : relative = diskPhysicalTransverseProjection relative +
      diskRadialMean relative • standardCircleBanach := by
    have actual := diskPhysical_relabel_neutral_decomposition relative
    rw [kernel, diskAreaMeanComponent_eq_real_smul] at actual
    have cancellation : relative - (0 : PeriodicC1HolderHalf) = relative := by
      with_reducible exact sub_zero relative
    exact cancellation.symm.trans actual
  let linear := fderiv ℝ diskSpectralTubularArea (diskRelabelNeutralCLM increment)
  have linearIdentity : linear relative = diskSpectralAreaRadialCoefficient increment * diskRadialMean relative := by
    have actual := congrArg linear decomposition
    have killed := annihilates relative
    change linear (diskPhysicalTransverseProjection relative) = 0 at killed
    rw [map_add, map_smul, killed, zero_add] at actual
    change linear relative = diskRadialMean relative * diskSpectralAreaRadialCoefficient increment at actual
    exact actual.trans (mul_comm _ _)
  have derivativeIdentity : fderiv ℝ diskStationaryArea (diskRelabelNeutralCLM increment)
      (diskChartedSpectralCoordinates increment relative) =
      diskSpectralAreaRadialCoefficient increment * diskRadialMean relative :=
    (derivative relative).symm.trans linearIdentity
  have neutralIdentity : diskStationaryArea (diskRelabelNeutralCLM increment) = Real.pi := by
    change diskStationaryArea (diskSpectralTubularChart (diskRelabelNeutralCLM increment)) = Real.pi at stationary
    rwa [diskSpectralTubularChart_stationary] at stationary
  have valueIdentity := congrArg diskStationaryArea (diskSpectralTubularChart_fiber_identity increment)
  have remainderIdentity : diskSpectralAreaFiberRemainder (diskRelabelNeutralCLM increment) relative =
      diskStationaryArea (diskRelabelNeutralCLM increment + diskChartedSpectralCoordinates increment relative) -
        diskStationaryArea (diskRelabelNeutralCLM increment) -
          fderiv ℝ diskStationaryArea (diskRelabelNeutralCLM increment)
            (diskChartedSpectralCoordinates increment relative) := by
    dsimp only [diskSpectralAreaFiberRemainder, diskStationaryAreaTaylorRemainder]
    rw [diskRelabelNeutralCLM_idempotent, diskChartedSpectralCoordinates_neutral_parameter]
  change diskStationaryArea (diskSpectralTubularChart increment) - Real.pi = _
  dsimp only [relative] at derivativeIdentity remainderIdentity ⊢
  linarith only [valueIdentity, derivativeIdentity, neutralIdentity, remainderIdentity]

end

end EulerNonuniqueness.Paper
