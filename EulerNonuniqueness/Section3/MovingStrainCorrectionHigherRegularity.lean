import EulerNonuniqueness.Section3.MovingStrainHigherInputs
import EulerNonuniqueness.Section3.MovingStrainCorrectionRegularity
import EulerNonuniqueness.General.ComplexForcingHigherRegularity

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

theorem independentCentroidStrainNumeratorAt_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun data => independentCentroidStrainNumeratorAt data (independentStrainPrimitiveAt data))
      standardCircleBanach := by
  have derivativeRegular := independentCentroidStrainDerivativeAt_hasLipschitzDerivativeNear
  have quadraticRegular := contourIndependentQuadraticAt_hasLipschitzDerivativeNear
  have primitiveRegular := independentStrainPrimitiveAt_hasLipschitzDerivativeNear
  have inner := derivativeRegular.prodMk (quadraticRegular.prodMk primitiveRegular)
  have outer : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun data : (((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
        PeriodicC1HolderHalf × PeriodicC1HolderHalf) ×
        (((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
          (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
          PeriodicC1HolderHalf × PeriodicC1HolderHalf) ×
          (PeriodicC1HolderHalf × PeriodicC1HolderHalf))) =>
        EulerNonuniqueness.General.forcingLinearCoefficient data.1 data.2.1 data.2.2)
      (independentCentroidStrainDerivativeAt standardCircleBanach,
        (contourIndependentQuadraticAt standardCircleBanach, independentStrainPrimitiveAt standardCircleBanach)) := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.forcingLinearCoefficient_hasLipschitzDerivativeNear
        (Space := PeriodicC1HolderHalf × PeriodicC1HolderHalf) _
  unfold independentCentroidStrainNumeratorAt
  with_reducible_and_instances
    exact EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp
      (outer := fun data => EulerNonuniqueness.General.forcingLinearCoefficient data.1 data.2.1 data.2.2)
      (inner := fun data => (independentCentroidStrainDerivativeAt data,
        (contourIndependentQuadraticAt data, independentStrainPrimitiveAt data))) outer inner

theorem independentStrainLinearCorrectionAt_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear independentStrainLinearCorrectionAt standardCircleBanach := by
  have generatorRegular := independentDiskRotatingDerivativeAt_hasLipschitzDerivativeNear
  have numeratorRegular := independentCentroidStrainNumeratorAt_hasLipschitzDerivativeNear
  have inner := generatorRegular.prodMk numeratorRegular
  have outer : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun data : (((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
        PeriodicC1HolderHalf × PeriodicC1HolderHalf) ×
        ((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
          PeriodicC1HolderHalf × PeriodicC1HolderHalf)) =>
        EulerNonuniqueness.General.finiteSpectralHomologicalSolver
          (EulerNonuniqueness.General.complexCubicProjection data.1) independentDiskSpectralEigenvalue
          (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2) data.2)
      (independentDiskRotatingDerivativeAt standardCircleBanach,
        independentCentroidStrainNumeratorAt standardCircleBanach (independentStrainPrimitiveAt standardCircleBanach)) := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.complexCubicHomologicalSolver_hasLipschitzDerivativeNear
        (Space := PeriodicC1HolderHalf × PeriodicC1HolderHalf)
        independentDiskSpectralEigenvalue (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2) _
  unfold independentStrainLinearCorrectionAt independentDiskSpectralProjectionAt
  with_reducible_and_instances
    exact EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp
      (outer := fun data => EulerNonuniqueness.General.finiteSpectralHomologicalSolver
        (EulerNonuniqueness.General.complexCubicProjection data.1) independentDiskSpectralEigenvalue
        (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2) data.2)
      (inner := fun data => (independentDiskRotatingDerivativeAt data,
        independentCentroidStrainNumeratorAt data (independentStrainPrimitiveAt data))) outer inner

end EulerNonuniqueness.Paper
