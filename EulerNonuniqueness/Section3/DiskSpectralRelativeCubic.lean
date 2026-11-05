import EulerNonuniqueness.Section3.DiskSpectralRelativeRawCubic
import EulerNonuniqueness.Section3.DiskSpectralRelativeCubicIdentity
import EulerNonuniqueness.General.LocalRelativeCubicFiberError

namespace EulerNonuniqueness.Paper

noncomputable section

open Metric

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance spectralRelativeGroup : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete
  chartedUniformBilinearAddCommGroup chartedUniformBilinearAddCommMonoid chartedUniformBilinearModule
  chartedUniformThirdGroup chartedUniformThirdSpace

theorem diskSpectralTubularEulerField_exists_relative_cubic_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      ‖(diskSpectralTubularEulerField initial -
          diskRotatingDerivative (initial - diskRelabelNeutralCLM initial) - diskSpectralFiberQuadraticValue initial) -
        (diskSpectralTubularEulerField final -
          diskRotatingDerivative (final - diskRelabelNeutralCLM final) - diskSpectralFiberQuadraticValue final)‖ ≤ constant *
        ((‖initial - diskRelabelNeutralCLM initial‖ + ‖final - diskRelabelNeutralCLM final‖) ^ 2 *
          ‖(initial - diskRelabelNeutralCLM initial) - (final - diskRelabelNeutralCLM final)‖ +
        (‖initial - diskRelabelNeutralCLM initial‖ + ‖final - diskRelabelNeutralCLM final‖) ^ 3 * ‖initial - final‖) := by
  obtain ⟨rawRadius, rawPositive, rawConstant, rawNonnegative, rawBound⟩ :=
    diskSpectralRawFiberRemainder_exists_relative_cubic_ball
  obtain ⟨normConstant, normNonnegative, normBound⟩ := diskSpectralRawFiberRemainder_exists_uniform_cubic
  have outerRegular := diskSpectralTubularInverseDerivative_lipschitzNear
  have differentialRegular := diskSpectralFiberDifferential_lipschitzNear
  have bilinearRegular := diskSpectralFiberQuadraticBilinear_lipschitzNear
  have identity := diskSpectralTubularEulerField_eventually_relative_cubic_identity
  let error := fun increment : PeriodicC1HolderHalf => diskSpectralTubularEulerField increment -
    diskRotatingDerivative (increment - diskRelabelNeutralCLM increment) - diskSpectralFiberQuadraticValue increment
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_relative_cubic_fiber_error_ball
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskSpectralTubularInverseDerivative
      _ diskSpectralFiberQuadraticBilinear diskSpectralRawFiberRemainder error
      outerRegular differentialRegular bilinearRegular rawPositive rawNonnegative normNonnegative rawBound normBound identity

end

end EulerNonuniqueness.Paper
