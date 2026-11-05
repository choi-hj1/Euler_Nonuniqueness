import EulerNonuniqueness.Section3.MovingStrainCorrectionHigherRegularity
import EulerNonuniqueness.Section3.MovingStrainRealCorrection
import EulerNonuniqueness.General.RealifiedComplexOperatorRegularity
import EulerNonuniqueness.General.RealifiedComplexCoefficientRegularity

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace
  movingStrainPairBilinearGroup movingStrainPairBilinearSpace
  movingNumeratorRealOperatorSpace movingNumeratorRealBilinearSpace
  movingNumeratorInnerSpace movingNumeratorTupleSpace
  movingStrainHigherInputsC1Group

theorem movingStrainRealCorrectionCLM_hasLipschitzDerivativeNear (coefficient : ℂ) :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun data => movingStrainRealCorrectionCLM data coefficient) standardCircleBanach := by
  have inner := independentStrainLinearCorrectionAt_hasLipschitzDerivativeNear
  have outer := EulerNonuniqueness.General.realifiedComplexOperator_hasLipschitzDerivativeNear
    contourIndependentRealification contourIndependentEmbedding coefficient
    (independentStrainLinearCorrectionAt standardCircleBanach)
  unfold movingStrainRealCorrectionCLM
  exact EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp
    (outer := fun operator => EulerNonuniqueness.General.realifiedComplexOperator
      contourIndependentRealification contourIndependentEmbedding operator coefficient)
    (inner := independentStrainLinearCorrectionAt) outer inner

theorem movingStrainRealCorrectionCoefficient_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun data => EulerNonuniqueness.General.realifiedComplexCoefficientLift
        contourIndependentRealification contourIndependentEmbedding (independentStrainLinearCorrectionAt data))
      standardCircleBanach := by
  have inner := independentStrainLinearCorrectionAt_hasLipschitzDerivativeNear
  have outer := EulerNonuniqueness.General.realifiedComplexCoefficientLift_hasLipschitzDerivativeNear
    contourIndependentRealification contourIndependentEmbedding (independentStrainLinearCorrectionAt standardCircleBanach)
  exact EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp
    (outer := EulerNonuniqueness.General.realifiedComplexCoefficientLift
      contourIndependentRealification contourIndependentEmbedding)
    (inner := independentStrainLinearCorrectionAt) outer inner

theorem movingStrainRealCorrectionCoefficient_apply (data : PeriodicC1HolderHalf) (coefficient : ℂ) :
    EulerNonuniqueness.General.realifiedComplexCoefficientLift
      contourIndependentRealification contourIndependentEmbedding (independentStrainLinearCorrectionAt data) coefficient =
      movingStrainRealCorrectionCLM data coefficient := by
  unfold movingStrainRealCorrectionCLM
  exact EulerNonuniqueness.General.realifiedComplexCoefficientLift_apply
    contourIndependentRealification contourIndependentEmbedding (independentStrainLinearCorrectionAt data) coefficient

end EulerNonuniqueness.Paper
