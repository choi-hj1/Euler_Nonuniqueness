import EulerNonuniqueness.Section3.DiskSpectralAreaCoefficient
import EulerNonuniqueness.General.LocalUniformQuadraticRemainder
import EulerNonuniqueness.General.ScalarConstraintQuadraticMean

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter Metric
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskAreaMeanComponent_eq_real_smul (mean : ℝ) :
    c1Product standardCircleBanach (c1Constant (mean : ℂ)) = mean • standardCircleBanach := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change standardCircle label * (mean : ℂ) = mean • standardCircle label
  simp only [Complex.real_smul]
  ring

theorem diskSpectralTubularArea_exists_quadratic_relative_mean_bound :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ increment : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖ ≤ radius →
      diskSpectralTubularArea increment = Real.pi →
      |diskRadialMean (increment - diskRelabelNeutralCLM increment)| ≤
        constant * ‖increment - diskRelabelNeutralCLM increment‖ ^ 2 := by
  obtain ⟨taylorRadius, taylorPositive, taylorConstant, taylorNonnegative, taylor⟩ :=
    EulerNonuniqueness.General.HasLipschitzDerivativeNear.exists_uniform_quadratic_remainder
      (Space := PeriodicC1HolderHalf) (Target := ℝ) diskSpectralTubularArea
      diskSpectralTubularArea_hasLipschitzDerivativeNear
  have nearby : ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      Real.pi ≤ diskSpectralAreaRadialCoefficient increment ∧
      (∀ direction : PeriodicC1HolderHalf, fderiv ℝ diskSpectralTubularArea (diskRelabelNeutralCLM increment)
        (diskPhysicalTransverseProjection direction) = 0) ∧
      diskSpectralTubularArea (diskRelabelNeutralCLM increment) = Real.pi := by
    filter_upwards [diskSpectralAreaRadialCoefficient_eventually_positive,
      diskSpectralTubularArea_eventually_stationary_transverse_derivative_zero,
      diskSpectralTubularArea_eventually_neutral_value] with increment positive annihilates value
    exact ⟨positive, annihilates, value⟩
  obtain ⟨conditionRadius, conditionPositive, contained⟩ := Metric.mem_nhds_iff.mp nearby
  refine ⟨min taylorRadius (conditionRadius / 2), lt_min taylorPositive (by positivity),
    taylorConstant / Real.pi, div_nonneg taylorNonnegative Real.pi_pos.le, ?_⟩
  intro increment inside area
  let neutral := diskRelabelNeutralCLM increment
  let relative := increment - neutral
  have identity : neutral + relative = increment := by dsimp [relative]; abel
  have normInside : ‖increment‖ ≤ ‖neutral‖ + ‖relative‖ := by
    simpa only [identity] using norm_add_le neutral relative
  have conditions : Real.pi ≤ diskSpectralAreaRadialCoefficient increment ∧
      (∀ direction : PeriodicC1HolderHalf, fderiv ℝ diskSpectralTubularArea (diskRelabelNeutralCLM increment)
        (diskPhysicalTransverseProjection direction) = 0) ∧
      diskSpectralTubularArea (diskRelabelNeutralCLM increment) = Real.pi := contained (show increment ∈ ball (0 : PeriodicC1HolderHalf) conditionRadius by
    change dist increment (0 : PeriodicC1HolderHalf) < conditionRadius
    have distance : dist increment (0 : PeriodicC1HolderHalf) = ‖increment‖ := by
      with_reducible exact dist_zero_right increment
    rw [distance]
    have bound := inside.trans (min_le_right _ _)
    linarith)
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
  have sameValue : diskSpectralTubularArea (neutral + relative) = diskSpectralTubularArea neutral := by
    rw [identity, area]
    exact conditions.2.2.symm
  have error := taylor neutral relative (inside.trans (min_le_left _ _))
  have coefficient : Real.pi ≤ fderiv ℝ diskSpectralTubularArea neutral standardCircleBanach := conditions.1
  let scalar : PeriodicC1HolderHalf →L[ℝ] ℝ := fderiv ℝ diskSpectralTubularArea neutral
  with_reducible
    exact EulerNonuniqueness.General.scalar_constraint_quadratic_mean_bound
      (Space := PeriodicC1HolderHalf) diskSpectralTubularArea scalar neutral relative
      (diskPhysicalTransverseProjection relative) standardCircleBanach Real.pi_pos coefficient decomposition
      (conditions.2.1 relative) sameValue error

end

end EulerNonuniqueness.Paper
