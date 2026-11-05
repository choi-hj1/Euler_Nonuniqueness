import EulerNonuniqueness.Section3.IndependentForcingRealification

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace
  independentRealificationOutputGroup independentRealificationInputGroup

theorem originalRealification_scaled_value (coefficient : ℂ)
    (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) (label : ℝ) :
    (contourIndependentRealification (coefficient • pair)).val.1 label =
      coefficient * pair.1.val.1 label + star (coefficient * pair.2.val.1 label) := rfl

theorem independentForcingRealLinearCorrection_value (degree : ℕ) (coefficient : ℂ)
    (direction : PeriodicC1HolderHalf) (label : ℝ) :
    (independentForcingRealLinearCorrection degree coefficient direction).val.1 label =
      coefficient * (independentForcingLinearCorrection degree (contourIndependentEmbedding direction)).1.val.1 label +
        star (coefficient * (independentForcingLinearCorrection degree
          (contourIndependentEmbedding direction)).2.val.1 label) := by
  unfold independentForcingRealLinearCorrection
  with_reducible
    exact originalRealification_scaled_value coefficient
      (independentForcingLinearCorrection degree (contourIndependentEmbedding direction)) label

end

end EulerNonuniqueness.Paper
