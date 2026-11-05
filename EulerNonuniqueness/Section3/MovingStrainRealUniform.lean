import EulerNonuniqueness.Section3.MovingStrainRealCorrection
import EulerNonuniqueness.Section3.MovingStrainCorrectionRegularity
import EulerNonuniqueness.Section3.RelabeledDiskForcingAnalytic
import EulerNonuniqueness.General.RealifiedComplexOperatorDifference

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group independentRealificationOutputGroup
  independentRealificationInputGroup forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace movingCorrectionRealOperatorSpace

theorem movingStrainRealCorrectionCLM_exists_uniform_relabel_bounds :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ angular : PeriodicC1HolderHalf, ‖angular‖ ≤ radius → ∀ coefficient : ℂ,
        ‖movingStrainRealCorrectionCLM (diskRelabelCurve angular 1) coefficient‖ ≤ constant * ‖coefficient‖) ∧
      ∀ first second : PeriodicC1HolderHalf, ‖first‖ ≤ radius → ‖second‖ ≤ radius → ∀ coefficient : ℂ,
        ‖movingStrainRealCorrectionCLM (diskRelabelCurve first 1) coefficient -
          movingStrainRealCorrectionCLM (diskRelabelCurve second 1) coefficient‖ ≤
          constant * ‖coefficient‖ * ‖first - second‖ := by
  have circle : diskRelabelCurve 0 1 = standardCircleBanach := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rw [diskRelabelCurve_value]
    change Complex.exp ((1 : ℂ) * (Complex.I * 0)) * standardCircle label = standardCircle label
    simp
  have inner := EulerNonuniqueness.General.lipschitzNear_of_analyticAt (diskRelabelMap_analyticAt (0 : PeriodicC1HolderHalf))
  have outer : EulerNonuniqueness.General.LipschitzNear independentStrainLinearCorrectionAt (diskRelabelCurve 0 1) := by
    rw [circle]
    exact independentStrainLinearCorrectionAt_lipschitzNear
  have regular := EulerNonuniqueness.General.LipschitzNear.comp
    (inner := fun angular : PeriodicC1HolderHalf => diskRelabelCurve angular 1)
    (point := (0 : PeriodicC1HolderHalf)) outer inner
  obtain ⟨lipschitzConstant, neighborhood, nearby, lipschitz⟩ := regular
  obtain ⟨neighborhoodRadius, neighborhoodPositive, contained⟩ := Metric.mem_nhds_iff.mp nearby
  let radius := neighborhoodRadius / 2
  let family := fun angular : PeriodicC1HolderHalf => independentStrainLinearCorrectionAt (diskRelabelCurve angular 1)
  let bound := ‖family 0‖ + (lipschitzConstant : ℝ) * radius
  let constant := 2 * bound + 2 * (lipschitzConstant : ℝ) + 1
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have boundNonnegative : 0 ≤ bound := by dsimp [bound]; positivity
  have constantOne : 1 ≤ constant := by dsimp [constant]; linarith [lipschitzConstant.coe_nonneg]
  have member (angular : PeriodicC1HolderHalf) (small : ‖angular‖ ≤ radius) : angular ∈ neighborhood := by
    apply contained
    rw [Metric.mem_ball, dist_zero_right]
    have half : radius = neighborhoodRadius / 2 := rfl
    rw [half] at small
    linarith
  have familyBound (angular : PeriodicC1HolderHalf) (small : ‖angular‖ ≤ radius) : ‖family angular‖ ≤ bound := by
    have difference := lipschitz.norm_sub_le (member angular small) (member 0 (by simp; exact radiusPositive.le))
    simp only [sub_zero] at difference
    with_reducible_and_instances
      change ‖family angular - family 0‖ ≤ (lipschitzConstant : ℝ) * ‖angular‖ at difference
    have triangle := norm_add_le (family angular - family 0) (family 0)
    rw [sub_add_cancel] at triangle
    dsimp only [bound]
    exact triangle.trans (by
      have actual := difference.trans (mul_le_mul_of_nonneg_left small lipschitzConstant.coe_nonneg)
      simpa only [add_comm] using add_le_add_right actual ‖family 0‖)
  have twiceBound : 2 * bound ≤ constant := by dsimp [constant]; linarith [lipschitzConstant.coe_nonneg]
  have twiceLip : 2 * (lipschitzConstant : ℝ) ≤ constant := by dsimp [constant]; linarith
  refine ⟨radius, radiusPositive, constant, constantOne, ?_, ?_⟩
  · intro angular small coefficient
    have estimate := (movingStrainRealCorrectionCLM_norm_bound (diskRelabelCurve angular 1) coefficient).trans
      (mul_le_mul_of_nonneg_left (familyBound angular small) (by positivity))
    calc
      _ ≤ 2 * ‖coefficient‖ * bound := estimate
      _ ≤ constant * ‖coefficient‖ := by nlinarith [norm_nonneg coefficient]
  · intro first second firstSmall secondSmall coefficient
    have difference := lipschitz.norm_sub_le (member first firstSmall) (member second secondSmall)
    with_reducible_and_instances
      change ‖family first - family second‖ ≤ (lipschitzConstant : ℝ) * ‖first - second‖ at difference
    have actual : ‖movingStrainRealCorrectionCLM (diskRelabelCurve first 1) coefficient -
        movingStrainRealCorrectionCLM (diskRelabelCurve second 1) coefficient‖ ≤
        2 * ‖coefficient‖ * ‖family first - family second‖ := by
      unfold movingStrainRealCorrectionCLM
      with_reducible_and_instances
        exact EulerNonuniqueness.General.realifiedComplexOperator_difference_bound
          contourIndependentRealification contourIndependentEmbedding (family first) (family second) coefficient
          contourIndependentRealification_operatorNorm_le_two contourIndependentEmbedding_operatorNorm_le_one
    calc
      _ ≤ 2 * ‖coefficient‖ * ((lipschitzConstant : ℝ) * ‖first - second‖) :=
        by
          with_reducible_and_instances
            exact actual.trans (mul_le_mul_of_nonneg_left difference (by positivity))
      _ ≤ constant * ‖coefficient‖ * ‖first - second‖ := by
        have scaled := mul_le_mul_of_nonneg_right twiceLip (mul_nonneg (norm_nonneg coefficient) (norm_nonneg (first - second)))
        convert scaled using 1 <;> ring

end EulerNonuniqueness.Paper
