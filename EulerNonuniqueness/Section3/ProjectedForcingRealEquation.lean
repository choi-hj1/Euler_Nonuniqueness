import EulerNonuniqueness.Section3.ProjectedForcingTangentEquation
import EulerNonuniqueness.Section3.ActualIndependentForcingNumerator

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentTangentEquationC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem contourIndependentRealification_frequency (degree : ℕ) (coefficient : ℂ)
    (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    contourIndependentRealification
        ((coefficient * (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2)) • pair) =
      (((degree + 2 : ℕ) : ℝ) / 2) •
        contourIndependentRealification ((-Complex.I * coefficient) • pair) := by
  rw [← contourIndependentRealification.map_smul]
  congr 1
  rw [← algebraMap_smul ℂ (((degree + 2 : ℕ) : ℝ) / 2), smul_smul]
  congr 1
  push_cast
  ring

theorem projectedForcing_real_homological_equation (degree : ℕ) (coefficient : ℂ)
    (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule) :
    contourIndependentRealification
        ((coefficient * (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2)) •
          projectedIndependentForcingLinearCorrection degree direction) +
      contourIndependentRealification
        (coefficient • projectedIndependentForcingLinearCorrection degree (diskRotatingDerivative direction)) -
      diskRotatingDerivative (contourIndependentRealification
        (coefficient • projectedIndependentForcingLinearCorrection degree direction)) =
      coefficient • centeredForcingCircleDerivative degree
        (contourCentroidGaugeProjection standardCircleBanach direction) +
      (2 : ℝ) • contourVelocityQuadraticDerivativeCLM standardCircleBanach
        (contourCentroidGaugeProjection standardCircleBanach direction)
        (contourIndependentRealification (coefficient • independentForcingPrimitiveValue degree)) := by
  have equation := congrArg (fun pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf =>
      contourIndependentRealification (coefficient • pair))
    (projectedIndependentForcingLinearCorrection_equation degree direction member)
  simp only [smul_sub, smul_add, map_sub, map_add, smul_smul] at equation
  have generator : contourIndependentRealification
      (coefficient • independentDiskRotatingDerivative
        (projectedIndependentForcingLinearCorrection degree direction)) =
      diskRotatingDerivative (contourIndependentRealification
        (coefficient • projectedIndependentForcingLinearCorrection degree direction)) := by
    rw [← independentDiskRotatingDerivative.map_smul coefficient,
      contourIndependentRealification_generator]
  rw [generator, independentForcingLinearCoefficient_realification] at equation
  exact equation

theorem projectedForcing_actual_real_homological_equation (degree : ℕ) (coefficient : ℂ)
    (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule) :
    contourIndependentRealification
        ((coefficient * (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2)) •
          projectedIndependentForcingLinearCorrection degree direction) +
      contourIndependentRealification
        (coefficient • projectedIndependentForcingLinearCorrection degree (diskRotatingDerivative direction)) -
      diskRotatingDerivative (contourIndependentRealification
        (coefficient • projectedIndependentForcingLinearCorrection degree direction)) =
      fderiv ℝ (fun data : PeriodicC1HolderHalf => contourCentroidGaugeProjection data
        (coefficient • c1Conjugate (c1NaturalPower data (degree + 1)))) standardCircleBanach
        (contourCentroidGaugeProjection standardCircleBanach direction) +
      fderiv ℝ (fderiv ℝ diskEulerRotatingField) standardCircleBanach
        (contourCentroidGaugeProjection standardCircleBanach direction)
        (contourIndependentRealification (coefficient • independentForcingPrimitiveValue degree)) := by
  have actual := independentForcingLinearCoefficient_actual_numerator degree coefficient
    (contourCentroidGaugeProjection standardCircleBanach direction)
  rw [independentForcingLinearCoefficient_realification] at actual
  exact (projectedForcing_real_homological_equation degree coefficient direction member).trans actual

end

end EulerNonuniqueness.Paper
