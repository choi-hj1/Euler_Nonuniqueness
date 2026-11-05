import EulerNonuniqueness.Section3.IndependentNumeratorRealification
import EulerNonuniqueness.Section3.ProjectedPolynomialForcingJet
import EulerNonuniqueness.Section3.DiskRotatingSecondJet

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentNumeratorRealificationC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem independentForcingLinearCoefficient_actual_numerator (degree : ℕ)
    (coefficient : ℂ) (direction : PeriodicC1HolderHalf) :
    contourIndependentRealification
      (coefficient • independentForcingLinearCoefficient degree (contourIndependentEmbedding direction)) =
      fderiv ℝ (fun data : PeriodicC1HolderHalf => contourCentroidGaugeProjection data
        (coefficient • c1Conjugate (c1NaturalPower data (degree + 1)))) standardCircleBanach direction +
      fderiv ℝ (fderiv ℝ diskEulerRotatingField) standardCircleBanach direction
        (contourIndependentRealification (coefficient • independentForcingPrimitiveValue degree)) := by
  have first : fderiv ℝ (fun data : PeriodicC1HolderHalf => contourCentroidGaugeProjection data
      (coefficient • c1Conjugate (c1NaturalPower data (degree + 1)))) standardCircleBanach direction =
      coefficient • centeredForcingCircleDerivative degree direction := by
    rw [projectedPolynomialForcing_circle_firstJet]
    exact centeredForcingCoefficientDerivative_apply degree coefficient direction
  have second := diskEulerRotatingField_second_derivative_apply standardCircleBanach direction
    (contourIndependentRealification (coefficient • independentForcingPrimitiveValue degree))
    (by simp only [sub_self, norm_zero]; positivity)
  rw [first, second]
  exact independentForcingLinearCoefficient_realification degree direction coefficient

end

end EulerNonuniqueness.Paper
