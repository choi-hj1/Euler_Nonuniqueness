import EulerNonuniqueness.Section3.DiskSpectralAreaMeanConstraint
import EulerNonuniqueness.General.QuadraticMeanAbsorption

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskSpectralTubularArea_exists_transverse_absorption :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ increment : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖ ≤ radius →
      diskSpectralTubularArea increment = Real.pi →
      ‖increment - diskRelabelNeutralCLM increment‖ ≤
        2 * ‖diskPhysicalTransverseProjection (increment - diskRelabelNeutralCLM increment)‖ ∧
      |diskRadialMean (increment - diskRelabelNeutralCLM increment)| ≤
        constant * ‖diskPhysicalTransverseProjection (increment - diskRelabelNeutralCLM increment)‖ ^ 2 := by
  obtain ⟨radius, positive, constant, nonnegative, meanBound⟩ :=
    diskSpectralTubularArea_exists_quadratic_relative_mean_bound
  let coefficient := constant * ‖standardCircleBanach‖
  have coefficientNonnegative : 0 ≤ coefficient := mul_nonneg nonnegative (norm_nonneg _)
  have denominatorPositive : 0 < 2 * (coefficient + 1) := by positivity
  have tiny : coefficient * (1 / (2 * (coefficient + 1))) ≤ 1 / 2 := by
    rw [show coefficient * (1 / (2 * (coefficient + 1))) = coefficient / (2 * (coefficient + 1)) by ring]
    apply (div_le_iff₀ denominatorPositive).mpr
    linarith
  refine ⟨min radius (1 / (2 * (coefficient + 1))), lt_min positive (by positivity),
    4 * constant, by positivity, ?_⟩
  intro increment inside area
  let relative := increment - diskRelabelNeutralCLM increment
  have relativeNeutral : diskRelabelNeutralCLM relative = 0 := by
    have linearity : diskRelabelNeutralCLM (increment - diskRelabelNeutralCLM increment) =
        diskRelabelNeutralCLM increment - diskRelabelNeutralCLM (diskRelabelNeutralCLM increment) := by
      with_reducible exact map_sub diskRelabelNeutralCLM increment (diskRelabelNeutralCLM increment)
    change diskRelabelNeutralCLM (increment - diskRelabelNeutralCLM increment) = 0
    rw [linearity, diskRelabelNeutralCLM_idempotent]
    with_reducible exact sub_self (diskRelabelNeutralCLM increment)
  have decomposition : relative = diskPhysicalTransverseProjection relative +
      diskRadialMean relative • standardCircleBanach := by
    have actual := diskPhysical_relabel_neutral_decomposition relative
    rw [relativeNeutral, diskAreaMeanComponent_eq_real_smul] at actual
    have cancellation : relative - (0 : PeriodicC1HolderHalf) = relative := by
      with_reducible exact sub_zero relative
    exact cancellation.symm.trans actual
  have relativeSmall : ‖relative‖ ≤ 1 / (2 * (coefficient + 1)) := by
    have bound := inside.trans (min_le_right _ _)
    have neutralNonnegative : 0 ≤ ‖diskRelabelNeutralCLM increment‖ := norm_nonneg _
    dsimp only [relative]
    linarith
  have small : constant * ‖standardCircleBanach‖ * ‖relative‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left relativeSmall coefficientNonnegative).trans tiny
  with_reducible
    exact EulerNonuniqueness.General.quadratic_mean_absorption relative
      (diskPhysicalTransverseProjection relative) standardCircleBanach (diskRadialMean relative)
      constant nonnegative decomposition (meanBound increment (inside.trans (min_le_left _ _)) area) small

end

end EulerNonuniqueness.Paper
