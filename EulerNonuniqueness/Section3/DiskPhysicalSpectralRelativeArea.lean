import EulerNonuniqueness.Section3.DiskPhysicalSpectralRelativeShape
import EulerNonuniqueness.Section3.DiskSpectralRelativeMean
import EulerNonuniqueness.Section3.DiskSpectralPhysicalSelfDecomposition
import EulerNonuniqueness.General.LocalRelativePhysicalLinear

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance physicalRelativeAreaC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskPhysicalSpectralDefect_exists_relative_physical_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ‖diskPhysicalSpectralDefect initial - diskPhysicalSpectralDefect final‖ ≤ constant *
        (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) := by
  have rawRelative := diskPhysicalSpectralDefect_exists_relative_linear_ball
  have relativeMean := diskSpectralTubularArea_exists_relative_mean_ball
  have absorption := diskSpectralTubularArea_exists_transverse_absorption
  have decomposition := diskSpectralRelative_transverse_mean_decomposition
  have estimate : ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      let first := diskPhysicalTransverseProjection (initial - diskRelabelNeutralCLM initial)
      let second := diskPhysicalTransverseProjection (final - diskRelabelNeutralCLM final)
      ‖diskPhysicalSpectralDefect initial - diskPhysicalSpectralDefect final‖ ≤ constant *
        (‖first - second‖ + (‖first‖ + ‖second‖) *
          ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.exists_relative_physical_linear_ball
        diskRelabelNeutralCLM diskPhysicalTransverseProjection standardCircleBanach diskRadialMean
        diskSpectralTubularArea diskPhysicalSpectralDefect Real.pi rawRelative relativeMean absorption decomposition
  simpa only [diskSpectralPhysicalTransverse_eq_projection] using estimate

end EulerNonuniqueness.Paper
