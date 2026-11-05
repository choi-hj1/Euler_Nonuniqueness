import EulerNonuniqueness.Section3.DiskSpectralUniformCubic
import EulerNonuniqueness.Section3.DiskSpectralAreaAbsorption
import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticBounds
import EulerNonuniqueness.Section3.DiskSpectralProjectionGenerator
import EulerNonuniqueness.General.QuadraticArgumentCubicReplacement
import EulerNonuniqueness.General.MeanComponentQuadraticNorm

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter Metric
open scoped Topology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralTubularEulerField_exists_area_transverse_cubic :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ increment : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖ ≤ radius →
      diskSpectralTubularArea increment = Real.pi →
      let transverse := diskPhysicalTransverseProjection (increment - diskRelabelNeutralCLM increment)
      ‖diskSpectralTubularEulerField increment - diskRotatingDerivative transverse -
        diskSpectralFiberQuadraticBilinear increment transverse transverse‖ ≤ constant * ‖transverse‖ ^ 3 := by
  obtain ⟨remainderConstant, remainderNonnegative, remainderEstimate⟩ :=
    diskSpectralTubularEulerField_exists_uniform_transverse_cubic
  obtain ⟨bilinearConstant, bilinearNonnegative, bilinearEstimate⟩ :=
    diskSpectralFiberQuadraticBilinear_exists_uniform_norm_bound
  obtain ⟨areaRadius, areaPositive, meanConstant, meanNonnegative, areaEstimate⟩ :=
    diskSpectralTubularArea_exists_transverse_absorption
  have nearby : ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskSpectralTubularEulerField increment -
        diskRotatingDerivative (increment - diskRelabelNeutralCLM increment) -
        diskSpectralFiberQuadraticValue increment‖ ≤
          remainderConstant * ‖increment - diskRelabelNeutralCLM increment‖ ^ 3 ∧
      ‖diskSpectralFiberQuadraticBilinear increment‖ ≤ bilinearConstant :=
    remainderEstimate.and bilinearEstimate
  obtain ⟨conditionRadius, conditionPositive, contained⟩ := Metric.mem_nhds_iff.mp nearby
  let meanBound := meanConstant * ‖standardCircleBanach‖
  have meanBoundNonnegative : 0 ≤ meanBound := mul_nonneg meanNonnegative (norm_nonneg _)
  refine ⟨min areaRadius (conditionRadius / 2), lt_min areaPositive (by positivity),
    8 * remainderConstant + 3 * bilinearConstant * meanBound, by positivity, ?_⟩
  intro increment inside area
  let relative := increment - diskRelabelNeutralCLM increment
  let transverse := diskPhysicalTransverseProjection relative
  have sumIdentity : diskRelabelNeutralCLM increment + relative = increment := by
    dsimp only [relative]
    abel
  have normBound : ‖increment‖ ≤ ‖diskRelabelNeutralCLM increment‖ + ‖relative‖ := by
    simpa only [sumIdentity] using norm_add_le (diskRelabelNeutralCLM increment) relative
  have conditions :
      ‖diskSpectralTubularEulerField increment - diskRotatingDerivative relative -
        diskSpectralFiberQuadraticValue increment‖ ≤ remainderConstant * ‖relative‖ ^ 3 ∧
      ‖diskSpectralFiberQuadraticBilinear increment‖ ≤ bilinearConstant :=
    contained (show increment ∈ ball (0 : PeriodicC1HolderHalf) conditionRadius by
      rw [Metric.mem_ball]
      have distance : dist increment (0 : PeriodicC1HolderHalf) = ‖increment‖ := by
        with_reducible exact dist_zero_right increment
      rw [distance]
      have small := inside.trans (min_le_right _ _)
      linarith)
  have absorption := areaEstimate increment (inside.trans (min_le_left _ _)) area
  have absorbed : ‖relative‖ ≤ 2 * ‖transverse‖ := absorption.1
  have kernel : diskRelabelNeutralCLM relative = 0 := by
    with_reducible
      exact EulerNonuniqueness.General.projection_relative_kernel (Space := PeriodicC1HolderHalf)
        diskRelabelNeutralCLM diskRelabelNeutralCLM_idempotent increment
  have decomposition : relative = transverse + diskRadialMean relative • standardCircleBanach := by
    have actual := diskPhysical_relabel_neutral_decomposition relative
    rw [kernel, diskAreaMeanComponent_eq_real_smul] at actual
    have cancellation : relative - (0 : PeriodicC1HolderHalf) = relative := by
      with_reducible exact sub_zero relative
    exact cancellation.symm.trans actual
  have difference : ‖relative - transverse‖ ≤ meanBound * ‖transverse‖ ^ 2 := by
    with_reducible
      exact EulerNonuniqueness.General.mean_component_quadratic_norm_le (Space := PeriodicC1HolderHalf)
        relative transverse standardCircleBanach decomposition absorption.2
  have replacement :
      ‖diskSpectralFiberQuadraticBilinear increment relative relative -
        diskSpectralFiberQuadraticBilinear increment transverse transverse‖ ≤
          3 * bilinearConstant * meanBound * ‖transverse‖ ^ 3 := by
    let bilinear : EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
      diskSpectralFiberQuadraticBilinear increment
    with_reducible
      exact EulerNonuniqueness.General.norm_bilinear_diagonal_sub_le_cubic (Space := PeriodicC1HolderHalf)
        bilinear relative transverse bilinearNonnegative meanBoundNonnegative conditions.2 absorption.1 difference
  have quadraticIdentity : diskSpectralFiberQuadraticValue increment =
      diskSpectralFiberQuadraticBilinear increment relative relative := by
    unfold diskSpectralFiberQuadraticValue
    rw [diskSpectralFiberQuadraticBilinear_apply]
  have rawBound := conditions.1
  rw [quadraticIdentity] at rawBound
  dsimp only
  rw [diskRotatingDerivative_transverse_projection]
  have errorIdentity : diskSpectralTubularEulerField increment - diskRotatingDerivative relative -
      diskSpectralFiberQuadraticBilinear increment transverse transverse =
      (diskSpectralTubularEulerField increment - diskRotatingDerivative relative -
        diskSpectralFiberQuadraticBilinear increment relative relative) +
      (diskSpectralFiberQuadraticBilinear increment relative relative -
        diskSpectralFiberQuadraticBilinear increment transverse transverse) := by abel
  rw [errorIdentity]
  apply (norm_add_le
    (diskSpectralTubularEulerField increment - diskRotatingDerivative relative -
      diskSpectralFiberQuadraticBilinear increment relative relative)
    (diskSpectralFiberQuadraticBilinear increment relative relative -
      diskSpectralFiberQuadraticBilinear increment transverse transverse)).trans
  apply (add_le_add rawBound replacement).trans
  have scalarBound : remainderConstant * ‖relative‖ ^ 3 +
      3 * bilinearConstant * meanBound * ‖transverse‖ ^ 3 ≤
        (8 * remainderConstant + 3 * bilinearConstant * meanBound) * ‖transverse‖ ^ 3 := by
    calc
      _ ≤ remainderConstant * (2 * ‖transverse‖) ^ 3 +
          3 * bilinearConstant * meanBound * ‖transverse‖ ^ 3 := by gcongr
      _ = _ := by ring
  simpa only [relative, transverse] using scalarBound

end

end EulerNonuniqueness.Paper
