import EulerNonuniqueness.Section3.DiskChartedRelativeCubic
import EulerNonuniqueness.Section3.DiskSpectralRawCubic
import EulerNonuniqueness.General.ScaledFiberRelativeCubic
import EulerNonuniqueness.General.LocalRelativeFiberTaylor

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance relativeRawGroup : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  relabelNeutralHolderSpace relabelNeutralC1Space
  diskChartedEulerRealSpace diskChartedEulerOperatorGroup diskChartedEulerOperatorSpace
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerUniformGroup diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete
  chartedUniformBilinearAddCommGroup chartedUniformBilinearAddCommMonoid chartedUniformBilinearModule
  chartedUniformThirdGroup chartedUniformThirdSpace

theorem diskSpectralRawFiberRemainder_eventually_taylor_identity :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      diskSpectralRawFiberRemainder increment =
        diskChartedEulerTaylorRemainder (diskRelabelNeutralCLM increment)
          (diskChartedSpectralCoordinates increment (increment - diskRelabelNeutralCLM increment)) := by
  filter_upwards [diskChartedEulerField_eventually_neutral_stationary,
    diskChartedSpectralCoordinates_eventually_conjugacy] with increment stationary equivalent
  obtain ⟨coordinates, identity, conjugacy⟩ := equivalent
  let relative := increment - diskRelabelNeutralCLM increment
  have intertwines : fderiv ℝ diskChartedEulerField (diskRelabelNeutralCLM increment)
      (diskChartedSpectralCoordinates increment relative) =
      diskChartedSpectralCoordinates increment (diskRotatingDerivative relative) := by
    have actual := congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf =>
      linear relative) conjugacy
    rw [← identity] at actual
    exact actual
  have algebra (value linear quadratic stationaryValue actualLinear : PeriodicC1HolderHalf)
      (zero : stationaryValue = 0) (same : actualLinear = linear) :
      value - linear - quadratic = value - stationaryValue - actualLinear - quadratic := by
    rw [zero, same]
    simp only [sub_zero]
  have imageIdentity := congrArg diskChartedEulerField
    (diskSpectralTubularChart_fiber_identity increment)
  have first := congrArg (fun value : PeriodicC1HolderHalf => value -
    diskChartedSpectralCoordinates increment (diskRotatingDerivative relative) -
      diskMovingQuadraticBilinear (diskRelabelNeutralCLM increment)
        (diskChartedSpectralCoordinates increment relative) (diskChartedSpectralCoordinates increment relative))
    imageIdentity
  have second := algebra
    (diskChartedEulerField (diskRelabelNeutralCLM increment + diskChartedSpectralCoordinates increment relative))
    (diskChartedSpectralCoordinates increment (diskRotatingDerivative relative))
    (diskMovingQuadraticBilinear (diskRelabelNeutralCLM increment)
      (diskChartedSpectralCoordinates increment relative) (diskChartedSpectralCoordinates increment relative))
    _ _ stationary intertwines
  dsimp only [diskSpectralRawFiberRemainder, diskChartedEulerTaylorRemainder]
  with_reducible_and_instances
    exact first.trans second

theorem diskSpectralRawFiberRemainder_exists_relative_cubic_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      ‖diskSpectralRawFiberRemainder initial - diskSpectralRawFiberRemainder final‖ ≤ constant *
        ((‖initial - diskRelabelNeutralCLM initial‖ + ‖final - diskRelabelNeutralCLM final‖) ^ 2 *
          ‖(initial - diskRelabelNeutralCLM initial) - (final - diskRelabelNeutralCLM final)‖ +
        (‖initial - diskRelabelNeutralCLM initial‖ + ‖final - diskRelabelNeutralCLM final‖) ^ 3 *
          ‖initial - final‖) := by
  obtain ⟨radius, positive, constant, relativeBound⟩ :=
    diskChartedEulerTaylorRemainder_exists_relative_cubic_ball
  have coordinateRegular := diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.lipschitzNear
  have identity := diskSpectralRawFiberRemainder_eventually_taylor_identity
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_relative_cubic_fiber_ball
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskChartedSpectralCoordinates
      diskChartedEulerTaylorRemainder diskSpectralRawFiberRemainder coordinateRegular
      positive constant.coe_nonneg relativeBound identity

end

end EulerNonuniqueness.Paper
