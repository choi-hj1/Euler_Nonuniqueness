import EulerNonuniqueness.Section3.DiskSpectralRelativeMean
import EulerNonuniqueness.Section3.DiskSpectralPhysicalSelfDecomposition
import EulerNonuniqueness.General.RelativeDecompositionBound

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance affineRelativeStateC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralTubularArea_exists_relative_state_bound :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ‖initial - final‖ ≤ constant *
        (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) := by
  obtain ⟨meanRadius, meanPositive, meanConstant, meanNonnegative, meanBound⟩ :=
    diskSpectralTubularArea_exists_relative_mean_ball
  have projectionNear : ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskPhysicalTransverseProjection state‖ < 1 / 2 := by
    have actual : ContinuousAt (fun state => diskPhysicalTransverseProjection state)
        (0 : PeriodicC1HolderHalf) := diskPhysicalTransverseProjection.continuous.continuousAt
    have convergence : Tendsto (fun state => ‖diskPhysicalTransverseProjection state‖)
        (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 (0 : ℝ)) := by
      simpa only [map_zero, norm_zero] using actual.norm.tendsto
    exact convergence.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨projectionRadius, projectionPositive, projectionContained⟩ := Metric.eventually_nhds_iff.mp projectionNear
  refine ⟨min meanRadius projectionRadius, lt_min meanPositive projectionPositive,
    1 + ‖standardCircleBanach‖ * meanConstant, by positivity, ?_⟩
  intro initial final initialInside finalInside initialArea finalArea
  have restrict {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 (min meanRadius projectionRadius))
      {outer : ℝ} (bound : min meanRadius projectionRadius ≤ outer) : state ∈ ball 0 outer :=
    ball_subset_ball bound inside
  have firstSize := projectionContained (by simpa only [mem_ball] using restrict initialInside (min_le_right _ _))
  have finalSize := projectionContained (by simpa only [mem_ball] using restrict finalInside (min_le_right _ _))
  have relativeMean := meanBound initial final (restrict initialInside (min_le_left _ _))
    (restrict finalInside (min_le_left _ _)) initialArea finalArea
  simp only [diskSpectralPhysicalTransverse_eq_projection] at relativeMean
  have firstDecomposition := diskSpectralRelative_transverse_mean_decomposition initial
  have finalDecomposition := diskSpectralRelative_transverse_mean_decomposition final
  simp only [diskSpectralPhysicalTransverse_eq_projection] at firstDecomposition finalDecomposition
  have relativeNorm := EulerNonuniqueness.General.norm_sub_le_of_scalar_decompositions
    (initial - diskRelabelNeutralCLM initial) (final - diskRelabelNeutralCLM final)
    (diskPhysicalTransverseProjection initial) (diskPhysicalTransverseProjection final) standardCircleBanach
    (diskRadialMean (initial - diskRelabelNeutralCLM initial))
    (diskRadialMean (final - diskRelabelNeutralCLM final)) firstDecomposition finalDecomposition
  have stateEquality : initial - final =
      (diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final) +
        ((initial - diskRelabelNeutralCLM initial) - (final - diskRelabelNeutralCLM final)) := by abel
  have stateNorm : ‖initial - final‖ ≤ ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖ +
      ‖(initial - diskRelabelNeutralCLM initial) - (final - diskRelabelNeutralCLM final)‖ := by
    rw [stateEquality]
    exact norm_add_le _ _
  have sizeSum : ‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖ ≤ 1 := by
    linarith
  have finalSquare : ‖diskPhysicalTransverseProjection final‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (diskPhysicalTransverseProjection final)]
  have meanSimple :
      |diskRadialMean (initial - diskRelabelNeutralCLM initial) -
        diskRadialMean (final - diskRelabelNeutralCLM final)| ≤ meanConstant *
          (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
            ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) := by
    apply relativeMean.trans
    apply mul_le_mul_of_nonneg_left _ meanNonnegative
    exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) sizeSum)
      (mul_le_of_le_one_right (norm_nonneg _) finalSquare)
  have combined := stateNorm.trans (add_le_add_left relativeNorm _)
  have meanProduct := mul_le_mul_of_nonneg_left meanSimple (norm_nonneg standardCircleBanach)
  nlinarith

end EulerNonuniqueness.Paper
