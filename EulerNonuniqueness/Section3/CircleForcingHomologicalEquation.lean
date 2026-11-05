import EulerNonuniqueness.Section3.IndependentForcingTangentEquation

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentTangentEquationC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem independentForcingLinearCorrection_operator_tangent_equation (degree : ℕ)
    (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule)
    (centered : fderiv ℝ contourCentroidFunctional standardCircleBanach direction = 0) :
    EulerNonuniqueness.General.linearHomologicalOperator independentDiskRotatingDerivative
      (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) (independentForcingLinearCorrection degree)
      (contourIndependentEmbedding direction) =
      independentForcingLinearCoefficient degree (contourIndependentEmbedding direction) := by
  unfold EulerNonuniqueness.General.linearHomologicalOperator
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, independentDiskRotatingDerivative_embedding]
  exact independentForcingLinearCorrection_tangent_equation degree direction member centered

end EulerNonuniqueness.Paper
