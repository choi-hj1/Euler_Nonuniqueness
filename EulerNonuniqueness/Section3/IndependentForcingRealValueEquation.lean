import EulerNonuniqueness.Section3.ProjectedForcingRealEquation

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentTangentEquationC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def independentForcingRealPrimitiveValue (degree : ℕ) (coefficient : ℂ) : PeriodicC1HolderHalf :=
  contourIndependentRealification (coefficient • independentForcingPrimitiveValue degree)

theorem projectedPolynomialForcing_circle_value (degree : ℕ) (coefficient : ℂ) :
    contourCentroidGaugeProjection standardCircleBanach
      (coefficient • c1Conjugate (c1NaturalPower standardCircleBanach (degree + 1))) =
      coefficient • c1Conjugate (diskCircleMode (degree + 1)) := by
  rw [contourCentroidGaugeProjection_complexPolynomial standardCircleBanach degree coefficient (by simp)]
  unfold areaNormalizedAntiholomorphicForcing
  rw [contourPolynomialMoment_circle_positive, star_zero, zero_div]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change coefficient * (star ((c1NaturalPower standardCircleBanach (degree + 1)).val.1 label) - 0) =
    coefficient * star ((diskCircleMode (degree + 1)).val.1 label)
  rw [c1NaturalPower_value, diskCircleMode_value, sub_zero]
  rfl

theorem independentForcingRealPrimitiveValue_actual_equation (degree : ℕ) (coefficient : ℂ) :
    (((degree + 2 : ℕ) : ℝ) / 2) • independentForcingRealPrimitiveValue degree (-Complex.I * coefficient) -
      diskRotatingDerivative (independentForcingRealPrimitiveValue degree coefficient) =
      contourCentroidGaugeProjection standardCircleBanach
        (coefficient • c1Conjugate (c1NaturalPower standardCircleBanach (degree + 1))) := by
  have equation := congrArg (fun pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf =>
      contourIndependentRealification (coefficient • pair)) (independentForcingPrimitiveValue_equation degree)
  simp only [smul_sub, map_sub, smul_smul] at equation
  have generator : contourIndependentRealification
      (coefficient • independentDiskRotatingDerivative (independentForcingPrimitiveValue degree)) =
      diskRotatingDerivative (contourIndependentRealification
        (coefficient • independentForcingPrimitiveValue degree)) := by
    rw [← independentDiskRotatingDerivative.map_smul coefficient,
      contourIndependentRealification_generator]
  have source : contourIndependentRealification
      (coefficient • (c1Conjugate (diskCircleMode (degree + 1)), 0)) =
      coefficient • c1Conjugate (diskCircleMode (degree + 1)) := by
    change contourIndependentRealification
      (coefficient • c1Conjugate (diskCircleMode (degree + 1)), coefficient • (0 : PeriodicC1HolderHalf)) = _
    rw [smul_zero, contourIndependentRealification_positive]
  rw [generator, source, contourIndependentRealification_frequency] at equation
  rw [projectedPolynomialForcing_circle_value]
  exact equation

end

end EulerNonuniqueness.Paper
