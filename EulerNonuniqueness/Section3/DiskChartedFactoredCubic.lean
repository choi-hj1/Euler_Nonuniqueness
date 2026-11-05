import EulerNonuniqueness.Section3.DiskChartedNeutralStationarity
import EulerNonuniqueness.Section3.DiskChartedSecondUniform
import EulerNonuniqueness.Section3.DiskStationaryAreaAbsorption
import EulerNonuniqueness.General.QuadraticJetRemainderFactor

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

theorem diskChartedQuadraticBilinear_second_jet :
    fderiv ℝ (fderiv ℝ diskChartedEulerField) (0 : PeriodicC1HolderHalf) =
      diskChartedQuadraticBilinear + diskChartedQuadraticBilinear.flip := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  change fderiv ℝ (fderiv ℝ diskChartedEulerField) (0 : PeriodicC1HolderHalf) first second =
    diskChartedQuadraticBilinear first second + diskChartedQuadraticBilinear second first
  rw [diskChartedQuadraticBilinear_symmetric second first]
  rw [diskChartedQuadraticBilinear_apply, ← add_smul]
  norm_num

theorem diskChartedEulerField_exists_factored_cubic_bound :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ increment : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖ ≤ radius →
      diskStationaryArea increment = Real.pi →
      ‖diskChartedEulerField increment - diskRotatingDerivative increment -
        diskChartedQuadraticBilinear increment increment‖ ≤
        constant * (‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖) ^ 2 *
          ‖diskPhysicalTransverseProjection increment‖ := by
  obtain ⟨regularRadius, regularPositive, constant, regular, lipschitz⟩ :=
    diskChartedEulerField_exists_second_lipschitz_ball
  obtain ⟨stationaryRadius, stationaryPositive, stationary⟩ :=
    Metric.mem_nhds_iff.mp diskChartedEulerField_eventually_neutral_stationary
  obtain ⟨absorptionRadius, absorptionPositive, absorption⟩ :=
    diskStationaryArea_exists_transverse_norm_absorption
  refine ⟨min regularRadius (min (stationaryRadius / 2) absorptionRadius),
    lt_min regularPositive (lt_min (by positivity) absorptionPositive), 2 * (constant : ℝ), by positivity, ?_⟩
  intro increment inside area
  have regularInside : ‖diskRelabelNeutralCLM increment‖ +
      ‖increment - diskRelabelNeutralCLM increment‖ ≤ regularRadius := inside.trans (min_le_left _ _)
  have normInside : ‖increment‖ ≤ ‖diskRelabelNeutralCLM increment‖ +
      ‖increment - diskRelabelNeutralCLM increment‖ := by
    have actual := norm_add_le (diskRelabelNeutralCLM increment) (increment - diskRelabelNeutralCLM increment)
    have identity : diskRelabelNeutralCLM increment + (increment - diskRelabelNeutralCLM increment) = increment := by abel
    rwa [identity] at actual
  have stationaryAt : diskChartedEulerField (diskRelabelNeutralCLM increment) = 0 := by
    apply stationary
    change dist increment (0 : PeriodicC1HolderHalf) < stationaryRadius
    have distance : dist increment (0 : PeriodicC1HolderHalf) = ‖increment‖ := by
      with_reducible exact dist_zero_right increment
    rw [distance]
    have half := inside.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have kernel : diskRotatingDerivative (diskRelabelNeutralCLM increment) = 0 := by
    rw [diskRelabelNeutralCLM_apply, ← diskRelabel_tangent_eq_material]
    exact diskRotatingDerivative_relabel_tangent_zero _ (diskNeutralCLM_real increment)
  have quadraticZero : diskChartedQuadraticBilinear (diskRelabelNeutralCLM increment)
      (diskRelabelNeutralCLM increment) = 0 := by
    rw [diskRelabelNeutralCLM_apply]
    exact diskChartedQuadraticBilinear_relabel_diagonal_zero _ (diskNeutralCLM_real increment)
  have factored :
      ‖diskChartedEulerField (diskRelabelNeutralCLM increment + (increment - diskRelabelNeutralCLM increment)) -
        diskRotatingDerivative (diskRelabelNeutralCLM increment + (increment - diskRelabelNeutralCLM increment)) -
        diskChartedQuadraticBilinear (diskRelabelNeutralCLM increment + (increment - diskRelabelNeutralCLM increment))
          (diskRelabelNeutralCLM increment + (increment - diskRelabelNeutralCLM increment))‖ ≤
      (constant : ℝ) * (‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖) ^ 2 *
        ‖increment - diskRelabelNeutralCLM increment‖ := by
    with_reducible
      exact EulerNonuniqueness.General.quadratic_jet_remainder_transverse_factor_of_fderiv
        (Space := PeriodicC1HolderHalf) diskChartedEulerField diskRotatingDerivative diskChartedQuadraticBilinear
        regularPositive.le constant regular lipschitz diskChartedEulerField_fderiv_zero
        diskChartedQuadraticBilinear_second_jet _ _ regularInside stationaryAt kernel quadraticZero
  have identity : diskRelabelNeutralCLM increment + (increment - diskRelabelNeutralCLM increment) = increment := by abel
  rw [identity] at factored
  have relative := absorption increment
    (inside.trans ((min_le_right _ _).trans (min_le_right _ _))) area
  exact factored.trans ((mul_le_mul_of_nonneg_left relative (by positivity)).trans_eq (by ring))

end

end EulerNonuniqueness.Paper
