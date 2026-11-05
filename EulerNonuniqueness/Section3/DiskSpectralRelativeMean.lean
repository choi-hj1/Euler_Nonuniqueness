import EulerNonuniqueness.Section3.DiskSpectralAreaFiberIdentity
import EulerNonuniqueness.Section3.DiskSpectralAreaCoefficientLipschitz
import EulerNonuniqueness.General.RelativeScalarConstraint
import EulerNonuniqueness.General.RelativeDecompositionBound
import EulerNonuniqueness.General.LocalRelativeScalarConstraint
import EulerNonuniqueness.Section3.DiskSpectralRelativeDecomposition

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter Metric
open scoped Topology

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd chartedBilinearGroup chartedBilinearModule

local instance spectralRelativeMeanGroup : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralTubularArea_exists_relative_mean_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      let initialRelative := initial - diskRelabelNeutralCLM initial
      let finalRelative := final - diskRelabelNeutralCLM final
      let first := diskPhysicalTransverseProjection initialRelative
      let second := diskPhysicalTransverseProjection finalRelative
      |diskRadialMean initialRelative - diskRadialMean finalRelative| ≤ constant *
        ((‖first‖ + ‖second‖) * ‖first - second‖ +
          ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖ * ‖second‖ ^ 2) := by
  have relativeRemainder := diskSpectralAreaFiberRemainder_exists_relative_quadratic_ball
  have absoluteAbsorption := diskSpectralTubularArea_exists_transverse_absorption
  have coefficientRegular := diskSpectralAreaRadialCoefficient_lipschitzNear
  have coefficientNeutral := diskSpectralAreaRadialCoefficient_neutral_parameter
  have positiveCoefficient := diskSpectralAreaRadialCoefficient_eventually_positive
  have meanIdentity := diskSpectralTubularArea_eventually_fiber_mean_identity
  have decomposition := diskSpectralRelative_transverse_mean_decomposition
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_relative_mean_ball
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskPhysicalTransverseProjection standardCircleBanach
      diskRadialMean diskSpectralAreaRadialCoefficient diskSpectralTubularArea diskSpectralAreaFiberRemainder
      Real.pi_pos relativeRemainder absoluteAbsorption coefficientRegular coefficientNeutral
      positiveCoefficient meanIdentity decomposition

end

end EulerNonuniqueness.Paper
