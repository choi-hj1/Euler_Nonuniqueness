import EulerNonuniqueness.Section3.DiskSpectralRelativeCubic
import EulerNonuniqueness.Section3.DiskSpectralRelativeMean
import EulerNonuniqueness.General.LocalRelativePhysicalCubic

namespace EulerNonuniqueness.Paper

noncomputable section

open Metric

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd chartedBilinearGroup chartedBilinearModule

local instance spectralPhysicalRelativeGroup : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskSpectralTubularCubicRemainder (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskSpectralTubularEulerField increment - diskRotatingDerivative (increment - diskRelabelNeutralCLM increment) -
    diskSpectralFiberQuadraticValue increment

theorem diskSpectralTubularCubicRemainder_exists_relative_physical_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      let first := diskPhysicalTransverseProjection (initial - diskRelabelNeutralCLM initial)
      let second := diskPhysicalTransverseProjection (final - diskRelabelNeutralCLM final)
      ‖diskSpectralTubularCubicRemainder initial - diskSpectralTubularCubicRemainder final‖ ≤ constant *
        ((‖first‖ + ‖second‖) ^ 2 * ‖first - second‖ +
          (‖first‖ + ‖second‖) ^ 3 * ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) := by
  have rawRelative := diskSpectralTubularEulerField_exists_relative_cubic_ball
  have relativeMean := diskSpectralTubularArea_exists_relative_mean_ball
  have absoluteAbsorption := diskSpectralTubularArea_exists_transverse_absorption
  have decomposition := diskSpectralRelative_transverse_mean_decomposition
  dsimp only [diskSpectralTubularCubicRemainder]
  let error := fun increment : PeriodicC1HolderHalf => diskSpectralTubularEulerField increment -
    diskRotatingDerivative (increment - diskRelabelNeutralCLM increment) - diskSpectralFiberQuadraticValue increment
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_relative_physical_cubic_ball
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskPhysicalTransverseProjection standardCircleBanach
      diskRadialMean diskSpectralTubularArea error Real.pi rawRelative relativeMean absoluteAbsorption decomposition

end

end EulerNonuniqueness.Paper
