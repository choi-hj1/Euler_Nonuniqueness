import EulerNonuniqueness.Section3.DiskChartedMixedResonance
import EulerNonuniqueness.Section3.DiskPhysicalResonance
import EulerNonuniqueness.Section3.DiskStationaryMeanDefect
import EulerNonuniqueness.General.QuadraticResonanceSymmetric
import EulerNonuniqueness.General.NeutralProjectedQuadraticBound

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

def diskChartedQuadraticResonance : EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.quadraticResonance diskPhysicalGroup (4 * Real.pi)
    diskChartedQuadraticBilinear

theorem diskChartedQuadraticResonance_symmetric (first second : PeriodicC1HolderHalf) :
    diskChartedQuadraticResonance first second = diskChartedQuadraticResonance second first := by
  apply EulerNonuniqueness.General.quadraticResonance_symmetric
  · with_reducible
      exact continuous_iff_continuousAt.mpr (fun time =>
        HasDerivAt.continuousAt (F := EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf)
          (EulerNonuniqueness.General.quadraticConjugate_hasDerivAt diskPhysicalGroup
            diskRotatingDerivative diskPhysicalGroup_zero diskPhysicalGroup_add
            diskPhysicalGroup_generator diskChartedQuadraticBilinear time))
  · exact diskChartedQuadraticBilinear_symmetric

theorem diskChartedQuadraticResonance_neutral_left (increment direction : PeriodicC1HolderHalf) :
    diskChartedQuadraticResonance (diskRelabelNeutralCLM increment) direction = 0 := by
  rw [diskRelabelNeutralCLM_apply]
  exact diskChartedQuadraticResonance_relabel_input_zero _ _ (diskNeutralCLM_real increment)

theorem diskChartedQuadraticResonance_neutral_right (increment direction : PeriodicC1HolderHalf) :
    diskChartedQuadraticResonance direction (diskRelabelNeutralCLM increment) = 0 := by
  rw [diskChartedQuadraticResonance_symmetric]
  exact diskChartedQuadraticResonance_neutral_left increment direction

theorem diskChartedQuadraticResonance_exists_projected_cubic_bound :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ increment : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖ ≤ radius →
      diskStationaryArea increment = Real.pi →
      ‖diskPhysicalTransverseProjection (diskChartedQuadraticResonance increment increment)‖ ≤
        constant * (‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖) *
          ‖diskPhysicalTransverseProjection increment‖ ^ 2 := by
  obtain ⟨meanRadius, meanPositive, meanConstant, meanNonnegative, meanBound⟩ :=
    diskStationaryArea_exists_projected_mean_defect_bound
  obtain ⟨absorptionRadius, absorptionPositive, absorptionBound⟩ :=
    diskStationaryArea_exists_transverse_norm_absorption
  refine ⟨min meanRadius absorptionRadius, lt_min meanPositive absorptionPositive,
    3 * ‖diskPhysicalTransverseProjection‖ * ‖diskChartedQuadraticResonance‖ * meanConstant,
    by positivity, ?_⟩
  intro increment inside area
  have transverseZero : diskPhysicalTransverseProjection
      (diskChartedQuadraticResonance (diskPhysicalTransverseProjection increment)
        (diskPhysicalTransverseProjection increment)) = 0 := by
    unfold diskChartedQuadraticResonance
    rw [show 4 * Real.pi = 2 * (2 * Real.pi) by ring]
    with_reducible
      exact EulerNonuniqueness.General.transverse_resonance_on_transverse_inputs_zero
        (Space := PeriodicC1HolderHalf) diskPhysicalGroup diskRotatingDerivative diskPhysicalTransverseProjection
        diskPhysicalGroup_zero diskPhysicalGroup_add diskPhysicalGroup_generator
        diskPhysicalTransverseProjection_group_commutes diskPhysicalTransverseProjection_idempotent
        diskPhysicalTransverseProjection_half.1 diskPhysicalTransverseProjection_half.2
        diskChartedQuadraticBilinear increment increment
  have actual :
      ‖diskPhysicalTransverseProjection (diskChartedQuadraticResonance
        (diskRelabelNeutralCLM increment + (increment - diskRelabelNeutralCLM increment))
        (diskRelabelNeutralCLM increment + (increment - diskRelabelNeutralCLM increment)))‖ ≤
      (3 * ‖diskPhysicalTransverseProjection‖ * ‖diskChartedQuadraticResonance‖ * meanConstant) *
        (‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖) *
          ‖diskPhysicalTransverseProjection increment‖ ^ 2 := by
    with_reducible
      exact EulerNonuniqueness.General.projected_quadratic_cubic_factor_of_mean_defect
        (Space := PeriodicC1HolderHalf) diskChartedQuadraticResonance diskPhysicalTransverseProjection
        (diskRelabelNeutralCLM increment) (increment - diskRelabelNeutralCLM increment)
        (diskPhysicalTransverseProjection increment)
        (diskChartedQuadraticResonance_neutral_left increment)
        (diskChartedQuadraticResonance_neutral_right increment)
        transverseZero
        (absorptionBound increment (inside.trans (min_le_right _ _)) area)
        (meanBound increment (inside.trans (min_le_left _ _)) area)
  have identity : diskRelabelNeutralCLM increment + (increment - diskRelabelNeutralCLM increment) = increment := by
    abel
  rw [identity] at actual
  exact actual

end

end EulerNonuniqueness.Paper
