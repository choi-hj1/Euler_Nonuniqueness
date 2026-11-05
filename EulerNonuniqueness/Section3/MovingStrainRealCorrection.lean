import EulerNonuniqueness.Section3.MovingStrainPrimitive
import EulerNonuniqueness.Section3.IndependentForcingRealification
import EulerNonuniqueness.General.RealifiedComplexOperatorApply

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group independentRealificationOutputGroup
  independentRealificationInputGroup forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem contourIndependentRealification_operatorNorm_le_two : ‖contourIndependentRealification‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro pair
  exact contourIndependentRealification_norm_le pair

theorem contourIndependentEmbedding_operatorNorm_le_one : ‖contourIndependentEmbedding‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro direction
  simpa only [one_mul] using contourIndependentEmbedding_norm_le direction

def movingStrainRealPrimitiveValue (data : PeriodicC1HolderHalf) (coefficient : ℂ) : PeriodicC1HolderHalf :=
  contourIndependentRealification (coefficient • independentStrainPrimitiveAt data)

def movingStrainRealCorrectionCLM (data : PeriodicC1HolderHalf) (coefficient : ℂ) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.realifiedComplexOperator contourIndependentRealification contourIndependentEmbedding
    (independentStrainLinearCorrectionAt data) coefficient

theorem movingStrainRealCorrectionCLM_apply (data direction : PeriodicC1HolderHalf) (coefficient : ℂ) :
    movingStrainRealCorrectionCLM data coefficient direction =
      contourIndependentRealification
        (coefficient • independentStrainLinearCorrectionAt data (contourIndependentEmbedding direction)) := by
  unfold movingStrainRealCorrectionCLM
  with_reducible_and_instances
    exact EulerNonuniqueness.General.realifiedComplexOperator_apply contourIndependentRealification
      contourIndependentEmbedding (independentStrainLinearCorrectionAt data) coefficient direction

theorem movingStrainRealCorrectionCLM_norm_bound (data : PeriodicC1HolderHalf) (coefficient : ℂ) :
    ‖movingStrainRealCorrectionCLM data coefficient‖ ≤
      2 * ‖coefficient‖ * ‖independentStrainLinearCorrectionAt data‖ := by
  unfold movingStrainRealCorrectionCLM
  with_reducible_and_instances
    exact EulerNonuniqueness.General.realifiedComplexOperator_norm_le_twice contourIndependentRealification
      contourIndependentEmbedding (independentStrainLinearCorrectionAt data) coefficient
      contourIndependentRealification_operatorNorm_le_two contourIndependentEmbedding_operatorNorm_le_one

end EulerNonuniqueness.Paper
