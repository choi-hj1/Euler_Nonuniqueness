import EulerNonuniqueness.Section3.MovingStrainAffineResidual
import EulerNonuniqueness.Section3.CentroidStrainProjectionJet

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group independentRealificationOutputGroup
  independentRealificationInputGroup forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem movingStrainAffineLinearResidualCLM_norm_bound (base : PeriodicC1HolderHalf) (coefficient : ℂ)
    (small : ‖base - standardCircleBanach‖ < 1 / 3) :
    ‖movingStrainAffineLinearResidualCLM base coefficient‖ ≤
      ‖coefficient‖ * ‖contourCentroidGaugeProjection base‖ +
      ‖fderiv ℝ (fderiv ℝ diskEulerRotatingField) base‖ * ‖movingStrainRealPrimitiveValue base coefficient‖ +
      2 * ‖fderiv ℝ diskEulerRotatingField base‖ * ‖movingStrainRealCorrectionCLM base coefficient‖ +
      ‖movingStrainRealCorrectionCLM base (-Complex.I * coefficient)‖ := by
  let sourceDerivative := fderiv ℝ (fun current : PeriodicC1HolderHalf => contourCentroidGaugeProjection current
    (coefficient • c1Conjugate current)) base
  let generator := fderiv ℝ diskEulerRotatingField base
  let second := fderiv ℝ (fderiv ℝ diskEulerRotatingField) base
  let correction := movingStrainRealCorrectionCLM base coefficient
  let partnerCorrection := movingStrainRealCorrectionCLM base (-Complex.I * coefficient)
  let value := movingStrainRealPrimitiveValue base coefficient
  have estimate := EulerNonuniqueness.General.affineResidualLinearOperator_norm_bound
    sourceDerivative generator correction partnerCorrection second value
  have sourceBound := projected_complex_strain_derivative_norm_bound base coefficient small
  have numerical := add_le_add_right (add_le_add_right (add_le_add_right sourceBound
    (‖second‖ * ‖value‖)) (2 * ‖generator‖ * ‖correction‖)) ‖partnerCorrection‖
  dsimp only [movingStrainAffineLinearResidualCLM]
  with_reducible_and_instances
    exact estimate.trans numerical

theorem movingStrainAffineLinearResidualCLM_apply_norm_le_defect (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (angularMember : angular ∈ contourContinuousVectorSubmodule)
    (nearby : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (coefficient : ℂ) (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule) :
    ‖movingStrainAffineLinearResidualCLM (fixedRelabelEquivalence angular small standardCircleBanach) coefficient direction‖ ≤
      ‖movingStrainAffineLinearResidualCLM (fixedRelabelEquivalence angular small standardCircleBanach) coefficient‖ *
        ‖contourCentroidGaugeProjection (fixedRelabelEquivalence angular small standardCircleBanach) direction - direction‖ := by
  let linear := movingStrainAffineLinearResidualCLM (fixedRelabelEquivalence angular small standardCircleBanach) coefficient
  let projection := contourCentroidGaugeProjection (fixedRelabelEquivalence angular small standardCircleBanach)
  have zero : linear (projection direction) = 0 := by
    dsimp only [linear, projection]
    with_reducible_and_instances
      exact movingStrainAffineLinearResidualCLM_projection_zero angular small angularMember nearby coefficient direction member
  have equality : linear direction = linear (direction - projection direction) := by
    rw [map_sub, zero, sub_zero]
  rw [equality]
  exact (linear.le_opNorm _).trans_eq (by rw [norm_sub_rev])

end EulerNonuniqueness.Paper
