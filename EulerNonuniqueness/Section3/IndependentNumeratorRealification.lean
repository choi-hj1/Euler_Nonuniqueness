import EulerNonuniqueness.Section3.IndependentForcingRealification
import EulerNonuniqueness.General.ComplexPairBilinearRealification

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance independentNumeratorRealificationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem contourIndependentRealification_quadratic (direction : PeriodicC1HolderHalf)
    (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) (coefficient : ℂ) :
    contourIndependentRealification
      (coefficient • contourIndependentQuadratic (contourIndependentEmbedding direction) pair) =
      contourVelocityQuadraticDerivativeCLM standardCircleBanach direction
        (contourIndependentRealification (coefficient • pair)) := by
  rw [contourIndependentRealification_eq_twice_real, contourIndependentRealification_eq_twice_real]
  unfold contourIndependentQuadratic contourIndependentEmbedding
  with_reducible
    exact EulerNonuniqueness.General.complexPairReal_scaled_bilinear_physical_left c1ConjugateCLM
      c1ConjugateCLM_complex_smul c1ConjugateCLM_involution
      (contourVelocityQuadraticDerivativeCLM standardCircleBanach) direction pair coefficient

theorem independentForcingLinearCoefficient_realification (degree : ℕ) (direction : PeriodicC1HolderHalf)
    (coefficient : ℂ) :
    contourIndependentRealification
      (coefficient • independentForcingLinearCoefficient degree (contourIndependentEmbedding direction)) =
      coefficient • centeredForcingCircleDerivative degree direction +
        (2 : ℝ) • contourVelocityQuadraticDerivativeCLM standardCircleBanach direction
          (contourIndependentRealification (coefficient • independentForcingPrimitiveValue degree)) := by
  have derivative := independentCenteredForcingDerivative_physical degree direction
  change independentCenteredForcingDerivative degree (contourIndependentEmbedding direction) =
    (centeredForcingCircleDerivative degree direction, 0) at derivative
  unfold independentForcingLinearCoefficient EulerNonuniqueness.General.forcingLinearCoefficient
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.flip_apply, smul_add, map_add]
  rw [derivative]
  have linearTerm : contourIndependentRealification
      (coefficient • (centeredForcingCircleDerivative degree direction, 0)) =
      coefficient • centeredForcingCircleDerivative degree direction := by
    change contourIndependentRealification
      (coefficient • centeredForcingCircleDerivative degree direction,
        coefficient • (0 : PeriodicC1HolderHalf)) = _
    rw [smul_zero, contourIndependentRealification_positive]
  rw [linearTerm]
  have quadratic := contourIndependentRealification_quadratic direction
    (independentForcingPrimitiveValue degree) coefficient
  simp only [two_smul ℂ, smul_add, map_add, quadratic, two_smul ℝ]

end

end EulerNonuniqueness.Paper
