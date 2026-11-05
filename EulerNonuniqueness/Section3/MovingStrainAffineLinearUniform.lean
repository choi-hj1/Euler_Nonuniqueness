import EulerNonuniqueness.Section3.MovingStrainAffineCoefficientRegularity
import EulerNonuniqueness.General.LocalLinearCoefficientBounds

noncomputable section

open Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace
  movingStrainPairBilinearGroup movingStrainPairBilinearSpace
  movingNumeratorRealOperatorSpace movingNumeratorRealBilinearSpace
  movingNumeratorInnerSpace movingNumeratorTupleSpace movingStrainHigherInputsC1Group
  strainSourceCoefficientDerivativeGroup strainSourceCoefficientDerivativeSpace
  centroidGaugeRegularityConstantGroup gaugeOperatorTaylorConstantSpace
  affineCoefficientOperatorGroup affineCoefficientOperatorModule affineCoefficientOperatorSpace

theorem movingStrainAffineLinearResidualCLM_exists_uniform_base_bounds :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ base : PeriodicC1HolderHalf, ‖base - standardCircleBanach‖ ≤ radius → ∀ coefficient : ℂ,
        ‖movingStrainAffineLinearResidualCLM base coefficient‖ ≤ constant * ‖coefficient‖) ∧
      ∀ initial final : PeriodicC1HolderHalf,
        ‖initial - standardCircleBanach‖ ≤ radius → ‖final - standardCircleBanach‖ ≤ radius →
        ∀ coefficient : ℂ,
        ‖movingStrainAffineLinearResidualCLM initial coefficient -
          movingStrainAffineLinearResidualCLM final coefficient‖ ≤
          constant * ‖coefficient‖ * ‖initial - final‖ := by
  have regular := movingStrainAffineLinearCoefficient_hasLipschitzDerivativeNear.lipschitzNear
  obtain ⟨outer, positive, constant, constantOne, absolute, difference⟩ :=
    regular.exists_uniform_linear_coefficient_ball
  have sourceNear := contourStrainSourceCoefficient_hasLipschitzSecondDerivativeNear.1.1
  obtain ⟨sourceRadius, sourcePositive, sourceContained⟩ := Metric.eventually_nhds_iff.mp sourceNear
  let radius := min outer (sourceRadius / 2)
  have radiusPositive : 0 < radius := lt_min positive (by positivity)
  have sourceRegular (base : PeriodicC1HolderHalf) (small : ‖base - standardCircleBanach‖ ≤ radius) :
      DifferentiableAt ℝ contourStrainSourceCoefficient base := by
    apply sourceContained
    rw [dist_eq_norm]
    exact small.trans_lt ((min_le_right _ _).trans_lt (by linarith))
  refine ⟨radius, radiusPositive, constant, constantOne, ?_, ?_⟩
  · intro base small coefficient
    have estimate := absolute base (small.trans (min_le_left _ _)) coefficient
    have equality := movingStrainAffineLinearCoefficient_apply base coefficient (sourceRegular base small)
    with_reducible_and_instances
      simpa only [equality] using estimate
  · intro initial final initialSmall finalSmall coefficient
    have estimate := difference initial final (initialSmall.trans (min_le_left _ _))
      (finalSmall.trans (min_le_left _ _)) coefficient
    have first := movingStrainAffineLinearCoefficient_apply initial coefficient (sourceRegular initial initialSmall)
    have second := movingStrainAffineLinearCoefficient_apply final coefficient (sourceRegular final finalSmall)
    with_reducible_and_instances
      simpa only [first, second] using estimate

end EulerNonuniqueness.Paper
