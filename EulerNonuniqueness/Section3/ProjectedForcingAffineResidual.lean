import EulerNonuniqueness.General.AffineForcingResidualJet
import EulerNonuniqueness.General.AffineResidualProjectionDefect
import EulerNonuniqueness.Section3.ProjectedForcingRealOperator
import EulerNonuniqueness.Section3.IndependentForcingRealValueEquation
import EulerNonuniqueness.Section3.ProjectedPolynomialForcingDerivative
import EulerNonuniqueness.Section3.DiskRotatingSecondFrechet

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentTangentEquationC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace
  independentRealificationC1Group independentRealificationOutputGroup independentRealificationInputGroup
  realCorrectionOperatorC1Group realCorrectionOperatorC1Semi realCorrectionRealOperatorGroup

def projectedPolynomialAffineCorrection (degree : ℕ) (coefficient : ℂ) :
    PeriodicC1HolderHalf → PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.affineForcingCorrection standardCircleBanach
    (independentForcingRealPrimitiveValue degree coefficient) (projectedForcingRealCorrectionCLM degree coefficient)

def projectedPolynomialAffineResidual (degree : ℕ) (coefficient : ℂ) :
    PeriodicC1HolderHalf → PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.realForcingResidual diskEulerRotatingField
    (fun data => contourCentroidGaugeProjection data (coefficient • c1Conjugate (c1NaturalPower data (degree + 1))))
    (projectedPolynomialAffineCorrection degree coefficient)
    (projectedPolynomialAffineCorrection degree (-Complex.I * coefficient)) (((degree + 2 : ℕ) : ℝ) / 2)

theorem projectedPolynomialAffineResidual_circle (degree : ℕ) (coefficient : ℂ) :
    projectedPolynomialAffineResidual degree coefficient standardCircleBanach = 0 := by
  have identity := EulerNonuniqueness.General.realForcingResidual_affine_value diskEulerRotatingField
    (fun data => contourCentroidGaugeProjection data (coefficient • c1Conjugate (c1NaturalPower data (degree + 1))))
    standardCircleBanach (independentForcingRealPrimitiveValue degree coefficient)
    (independentForcingRealPrimitiveValue degree (-Complex.I * coefficient)) diskRotatingDerivative
    (projectedForcingRealCorrectionCLM degree coefficient)
    (projectedForcingRealCorrectionCLM degree (-Complex.I * coefficient)) (((degree + 2 : ℕ) : ℝ) / 2)
    diskEulerRotatingField_hasFDerivAt_circle diskEulerRotatingField_circle
  unfold projectedPolynomialAffineResidual projectedPolynomialAffineCorrection
  rw [identity]
  dsimp only
  rw [← independentForcingRealPrimitiveValue_actual_equation degree coefficient]
  abel

theorem projectedPolynomialAffineResidual_fderiv (degree : ℕ) (coefficient : ℂ) :
    fderiv ℝ (projectedPolynomialAffineResidual degree coefficient) standardCircleBanach =
      fderiv ℝ (fun data : PeriodicC1HolderHalf => contourCentroidGaugeProjection data
        (coefficient • c1Conjugate (c1NaturalPower data (degree + 1)))) standardCircleBanach +
      (fderiv ℝ (fderiv ℝ diskEulerRotatingField) standardCircleBanach).flip
        (independentForcingRealPrimitiveValue degree coefficient) +
      diskRotatingDerivative.comp (projectedForcingRealCorrectionCLM degree coefficient) -
      (projectedForcingRealCorrectionCLM degree coefficient).comp diskRotatingDerivative -
      (((degree + 2 : ℕ) : ℝ) / 2) • projectedForcingRealCorrectionCLM degree (-Complex.I * coefficient) := by
  have small : ‖standardCircleBanach - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    simp only [sub_self, norm_zero]
    positivity
  have forcingSmall : ‖standardCircleBanach - standardCircleBanach‖ < (1 / 3 : ℝ) := by norm_num
  let forcingDerivative := fderiv ℝ (fun data : PeriodicC1HolderHalf => contourCentroidGaugeProjection data
    (coefficient • c1Conjugate (c1NaturalPower data (degree + 1)))) standardCircleBanach
  let second := fderiv ℝ (fderiv ℝ diskEulerRotatingField) standardCircleBanach
  have fieldJet := diskEulerRotatingField_hasFDerivAt_circle
  have secondJet := diskEulerRotatingField_hasFDerivAt_fderiv standardCircleBanach small
  have forcingJet := projectedPolynomialForcing_hasFDerivAt degree coefficient standardCircleBanach forcingSmall
  unfold projectedPolynomialAffineResidual projectedPolynomialAffineCorrection
  with_reducible_and_instances
    exact EulerNonuniqueness.General.realForcingResidual_affine_fderiv diskEulerRotatingField
      (fun data => contourCentroidGaugeProjection data (coefficient • c1Conjugate (c1NaturalPower data (degree + 1))))
      standardCircleBanach (independentForcingRealPrimitiveValue degree coefficient)
      (independentForcingRealPrimitiveValue degree (-Complex.I * coefficient)) diskRotatingDerivative
      forcingDerivative
      (projectedForcingRealCorrectionCLM degree coefficient)
      (projectedForcingRealCorrectionCLM degree (-Complex.I * coefficient))
      second (((degree + 2 : ℕ) : ℝ) / 2) fieldJet secondJet forcingJet

theorem projectedPolynomialAffineResidual_fderiv_apply (degree : ℕ) (coefficient : ℂ)
    (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule) :
    fderiv ℝ (projectedPolynomialAffineResidual degree coefficient) standardCircleBanach direction =
      fderiv ℝ (fun data : PeriodicC1HolderHalf => contourCentroidGaugeProjection data
        (coefficient • c1Conjugate (c1NaturalPower data (degree + 1)))) standardCircleBanach
        (direction - contourCentroidGaugeProjection standardCircleBanach direction) +
      fderiv ℝ (fderiv ℝ diskEulerRotatingField) standardCircleBanach
        (direction - contourCentroidGaugeProjection standardCircleBanach direction)
        (independentForcingRealPrimitiveValue degree coefficient) := by
  rw [projectedPolynomialAffineResidual_fderiv]
  let forcingDerivative := fderiv ℝ (fun data : PeriodicC1HolderHalf => contourCentroidGaugeProjection data
    (coefficient • c1Conjugate (c1NaturalPower data (degree + 1)))) standardCircleBanach
  let second := fderiv ℝ (fderiv ℝ diskEulerRotatingField) standardCircleBanach
  have sourceEquation := projectedForcingRealCorrectionCLM_actual_equation degree coefficient direction member
  have equation : (((degree + 2 : ℕ) : ℝ) / 2) • projectedForcingRealCorrectionCLM degree (-Complex.I * coefficient) direction +
      projectedForcingRealCorrectionCLM degree coefficient (diskRotatingDerivative direction) -
      diskRotatingDerivative (projectedForcingRealCorrectionCLM degree coefficient direction) =
    forcingDerivative (contourCentroidGaugeProjection standardCircleBanach direction) +
      second (contourCentroidGaugeProjection standardCircleBanach direction)
        (independentForcingRealPrimitiveValue degree coefficient) := by
    dsimp only [forcingDerivative, second, independentForcingRealPrimitiveValue]
    with_reducible_and_instances
      exact sourceEquation
  with_reducible_and_instances
   exact EulerNonuniqueness.General.affineResidual_projection_defect diskRotatingDerivative
    forcingDerivative
    (projectedForcingRealCorrectionCLM degree coefficient)
    (projectedForcingRealCorrectionCLM degree (-Complex.I * coefficient))
    (contourCentroidGaugeProjection standardCircleBanach)
    second
    (independentForcingRealPrimitiveValue degree coefficient) direction (((degree + 2 : ℕ) : ℝ) / 2) equation

end EulerNonuniqueness.Paper
