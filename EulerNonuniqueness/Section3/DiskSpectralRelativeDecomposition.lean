import EulerNonuniqueness.Section3.DiskSpectralAreaMeanConstraint

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd chartedBilinearGroup chartedBilinearModule

local instance spectralDecompositionGroup : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralRelative_neutral_zero (state : PeriodicC1HolderHalf) :
    diskRelabelNeutralCLM (state - diskRelabelNeutralCLM state) = 0 := by
  have linearity : diskRelabelNeutralCLM (state - diskRelabelNeutralCLM state) =
      diskRelabelNeutralCLM state - diskRelabelNeutralCLM (diskRelabelNeutralCLM state) := by
    with_reducible exact map_sub diskRelabelNeutralCLM state (diskRelabelNeutralCLM state)
  rw [linearity, diskRelabelNeutralCLM_idempotent]
  with_reducible exact sub_self (diskRelabelNeutralCLM state)

theorem diskSpectralRelative_transverse_mean_decomposition (state : PeriodicC1HolderHalf) :
    state - diskRelabelNeutralCLM state =
      diskPhysicalTransverseProjection (state - diskRelabelNeutralCLM state) +
        diskRadialMean (state - diskRelabelNeutralCLM state) • standardCircleBanach := by
  let relative := state - diskRelabelNeutralCLM state
  have kernel : diskRelabelNeutralCLM relative = 0 := diskSpectralRelative_neutral_zero state
  have actual := diskPhysical_relabel_neutral_decomposition relative
  rw [kernel, diskAreaMeanComponent_eq_real_smul] at actual
  have cancellation : relative - (0 : PeriodicC1HolderHalf) = relative := by
    with_reducible exact sub_zero relative
  with_reducible_and_instances
    exact cancellation.symm.trans actual

end

end EulerNonuniqueness.Paper
