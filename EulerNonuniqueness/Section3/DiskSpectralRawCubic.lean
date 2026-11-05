import EulerNonuniqueness.Section3.DiskSpectralFiberAlgebra
import EulerNonuniqueness.Section3.DiskMovingQuadraticTaylor
import EulerNonuniqueness.General.ScaledFiberTaylor

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

def diskSpectralRawFiberRemainder (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  let relative := increment - diskRelabelNeutralCLM increment
  let image := diskChartedSpectralCoordinates increment relative
  diskChartedEulerField (diskSpectralTubularChart increment) -
    diskChartedSpectralCoordinates increment (diskRotatingDerivative relative) -
      diskMovingQuadraticBilinear (diskRelabelNeutralCLM increment) image image

theorem diskSpectralRawFiberRemainder_exists_uniform_cubic :
    ∃ constant ≥ 0, ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskSpectralRawFiberRemainder increment‖ ≤
        constant * ‖increment - diskRelabelNeutralCLM increment‖ ^ 3 := by
  have continuous : ContinuousAt diskChartedSpectralCoordinates (0 : PeriodicC1HolderHalf) := by
    with_reducible
      exact diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.differentiableAt.continuousAt
  have intertwines : ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf), ∀ direction : PeriodicC1HolderHalf,
      fderiv ℝ diskChartedEulerField (diskRelabelNeutralCLM increment)
          (diskChartedSpectralCoordinates increment direction) =
        diskChartedSpectralCoordinates increment (diskRotatingDerivative direction) := by
    filter_upwards [diskChartedSpectralCoordinates_eventually_conjugacy] with increment equivalent direction
    obtain ⟨coordinates, identity, conjugacy⟩ := equivalent
    have actual := congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => linear direction) conjugacy
    rw [← identity] at actual
    exact actual
  unfold diskSpectralRawFiberRemainder
  simp_rw [diskSpectralTubularChart_fiber_identity]
  with_reducible
    exact EulerNonuniqueness.General.exists_eventually_scaled_fiber_taylor
      (Space := PeriodicC1HolderHalf) diskChartedEulerField diskMovingQuadraticBilinear
      diskRelabelNeutralCLM diskRotatingDerivative diskChartedSpectralCoordinates continuous
      diskChartedEulerField_exists_uniform_moving_quadratic_taylor
      diskChartedEulerField_eventually_neutral_stationary intertwines

end

end EulerNonuniqueness.Paper
