import EulerNonuniqueness.Section3.DiskSpectralRelativeMean
import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticLipschitz
import EulerNonuniqueness.General.LocalRelativeBilinearMeanError

namespace EulerNonuniqueness.Paper

noncomputable section

open Metric

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd chartedBilinearGroup chartedBilinearModule

local instance spectralRelativeMeanQuadraticGroup : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskSpectralFiberMeanQuadraticError (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  let relative := increment - diskRelabelNeutralCLM increment
  let transverse := diskPhysicalTransverseProjection relative
  diskSpectralFiberQuadraticBilinear increment relative relative -
    diskSpectralFiberQuadraticBilinear increment transverse transverse

theorem diskSpectralFiberMeanQuadraticError_exists_relative_physical_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      let first := diskPhysicalTransverseProjection (initial - diskRelabelNeutralCLM initial)
      let second := diskPhysicalTransverseProjection (final - diskRelabelNeutralCLM final)
      ‖diskSpectralFiberMeanQuadraticError initial - diskSpectralFiberMeanQuadraticError final‖ ≤ constant *
        ((‖first‖ + ‖second‖) ^ 2 * ‖first - second‖ +
          (‖first‖ + ‖second‖) ^ 3 * ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) := by
  have coefficientRegular := diskSpectralFiberQuadraticBilinear_lipschitzNear
  have coefficientNeutral := diskSpectralFiberQuadraticBilinear_neutral_parameter
  have relativeMean := diskSpectralTubularArea_exists_relative_mean_ball
  have absoluteAbsorption := diskSpectralTubularArea_exists_transverse_absorption
  have decomposition := diskSpectralRelative_transverse_mean_decomposition
  dsimp only [diskSpectralFiberMeanQuadraticError]
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_relative_bilinear_mean_error_ball
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskPhysicalTransverseProjection standardCircleBanach
      diskRadialMean diskSpectralTubularArea diskSpectralFiberQuadraticBilinear Real.pi
      coefficientRegular coefficientNeutral relativeMean absoluteAbsorption decomposition

end

end EulerNonuniqueness.Paper
