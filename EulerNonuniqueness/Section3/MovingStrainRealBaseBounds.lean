import EulerNonuniqueness.Section3.MovingStrainRealCorrection
import EulerNonuniqueness.Section3.MovingStrainCorrectionRegularity
import EulerNonuniqueness.General.RealifiedComplexOperatorLocalBounds

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group independentRealificationOutputGroup
  independentRealificationInputGroup forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace movingCorrectionRealOperatorSpace

theorem movingStrainRealCorrectionCLM_exists_uniform_base_bounds :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ point : PeriodicC1HolderHalf, ‖point - standardCircleBanach‖ ≤ radius → ∀ coefficient : ℂ,
        ‖movingStrainRealCorrectionCLM point coefficient‖ ≤ constant * ‖coefficient‖) ∧
      ∀ first second : PeriodicC1HolderHalf,
        ‖first - standardCircleBanach‖ ≤ radius → ‖second - standardCircleBanach‖ ≤ radius → ∀ coefficient : ℂ,
        ‖movingStrainRealCorrectionCLM first coefficient - movingStrainRealCorrectionCLM second coefficient‖ ≤
          constant * ‖coefficient‖ * ‖first - second‖ := by
  have regular : EulerNonuniqueness.General.LipschitzNear independentStrainLinearCorrectionAt
      standardCircleBanach := independentStrainLinearCorrectionAt_lipschitzNear
  unfold movingStrainRealCorrectionCLM
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_realifiedComplexOperator_uniform_local_bounds
      contourIndependentRealification contourIndependentEmbedding independentStrainLinearCorrectionAt standardCircleBanach
      regular contourIndependentRealification_operatorNorm_le_two contourIndependentEmbedding_operatorNorm_le_one

end EulerNonuniqueness.Paper
