import EulerNonuniqueness.Section3.MovingStrainRealEquation
import EulerNonuniqueness.Section3.ContourContinuousGauge
import EulerNonuniqueness.General.AffineResidualLinearOperator
import EulerNonuniqueness.General.AffineResidualQuadraticRemainder

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

def movingStrainAffineResidual (base : PeriodicC1HolderHalf) (coefficient : ℂ)
    (current : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  contourCentroidGaugeProjection current (coefficient • c1Conjugate current) +
    fderiv ℝ diskEulerRotatingField current
      (movingStrainRealPrimitiveValue base coefficient + movingStrainRealCorrectionCLM base coefficient (current - base)) -
    movingStrainRealCorrectionCLM base coefficient (diskEulerRotatingField current) -
    movingStrainRealPrimitiveValue base (-Complex.I * coefficient) -
    movingStrainRealCorrectionCLM base (-Complex.I * coefficient) (current - base)

def movingStrainAffineLinearResidualCLM (base : PeriodicC1HolderHalf) (coefficient : ℂ) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.affineResidualLinearOperator
    (fderiv ℝ (fun current : PeriodicC1HolderHalf => contourCentroidGaugeProjection current
      (coefficient • c1Conjugate current)) base)
    (fderiv ℝ diskEulerRotatingField base) (movingStrainRealCorrectionCLM base coefficient)
    (movingStrainRealCorrectionCLM base (-Complex.I * coefficient))
    (fderiv ℝ (fderiv ℝ diskEulerRotatingField) base) (movingStrainRealPrimitiveValue base coefficient)

theorem movingStrainAffineLinearResidualCLM_tangent_zero (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (angularMember : angular ∈ contourContinuousVectorSubmodule)
    (nearby : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (coefficient : ℂ) (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule)
    (centered : fderiv ℝ contourCentroidFunctional
      (fixedRelabelEquivalence angular small standardCircleBanach) direction = 0) :
    movingStrainAffineLinearResidualCLM (fixedRelabelEquivalence angular small standardCircleBanach) coefficient direction = 0 := by
  have actual := movingStrainRealCorrectionCLM_actual_tangent_equation angular small angularMember nearby coefficient direction member centered
  unfold movingStrainAffineLinearResidualCLM
  with_reducible_and_instances
    exact EulerNonuniqueness.General.affineResidualLinearOperator_apply_eq_zero _ _ _ _ _ _ direction actual

theorem movingStrainAffineLinearResidualCLM_projection_zero (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (angularMember : angular ∈ contourContinuousVectorSubmodule)
    (nearby : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (coefficient : ℂ) (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule) :
    movingStrainAffineLinearResidualCLM (fixedRelabelEquivalence angular small standardCircleBanach) coefficient
      (contourCentroidGaugeProjection (fixedRelabelEquivalence angular small standardCircleBanach) direction) = 0 :=
  movingStrainAffineLinearResidualCLM_tangent_zero angular small angularMember nearby coefficient _
    (contourContinuousVectorSubmodule_centroid_projection _ _ member)
    (contourCentroidGaugeProjection_centroid_zero _ _ (lt_min_iff.mp nearby).1)

end EulerNonuniqueness.Paper
