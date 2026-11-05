import EulerNonuniqueness.Section3.IndependentForcingResonance
import EulerNonuniqueness.Section3.CentroidCenteredStrainJet
import EulerNonuniqueness.Section3.HilbertContinuousVectors
import EulerNonuniqueness.Section3.DiskNormalizedTangentFourier

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance actualStrainResonanceC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def actualCentroidStrainCircleDerivative : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  fderiv ℝ centroidCenteredStrain standardCircleBanach

def actualIndependentCentroidStrainDerivative :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexPairPositiveExtension c1ConjugateCLM c1ConjugateCLM_complex_smul
    actualCentroidStrainCircleDerivative

theorem actualIndependentCentroidStrainDerivative_eq :
    actualIndependentCentroidStrainDerivative = independentCenteredForcingDerivative 0 := by
  have derivativeIdentity : actualCentroidStrainCircleDerivative = centeredForcingCircleDerivative 0 := by
    exact centroidCenteredStrain_firstJet
  unfold actualIndependentCentroidStrainDerivative independentCenteredForcingDerivative
  rw [derivativeIdentity]

def actualCentroidStrainLinearCoefficient :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.forcingLinearCoefficient actualIndependentCentroidStrainDerivative
    contourIndependentQuadratic (independentForcingPrimitiveValue 0)

def actualCentroidStrainRadialBlock : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.weightedOperatorBlock independentNegativeRadial
    actualCentroidStrainLinearCoefficient independentPositiveMaterial

theorem actualCentroidStrainRadialBlock_eq :
    actualCentroidStrainRadialBlock = independentForcingRadialBlock 0 := by
  unfold actualCentroidStrainRadialBlock actualCentroidStrainLinearCoefficient
    independentForcingRadialBlock independentForcingLinearCoefficient
  rw [actualIndependentCentroidStrainDerivative_eq]

theorem actualCentroidStrain_normalized_tangent_resonance_zero (direction : PeriodicC1HolderHalf)
    (member : direction ∈ contourContinuousVectorSubmodule)
    (centered : (fderiv ℝ contourCentroidFunctional standardCircleBanach) direction = 0) :
    periodicHilbertNegativeProjection
      (actualCentroidStrainRadialBlock (periodicHilbertPositiveProjection (diskRadialPart direction))) = 0 := by
  rw [actualCentroidStrainRadialBlock_eq]
  apply independentStrainForcing_resonant_positive_input
  · exact contourContinuousVectorSubmodule_positive_projection _
      (contourContinuousVectorSubmodule_radial direction member)
  · exact diskRadialPart_fourierCoeff_one_zero_of_centroid_tangent direction centered

end

end EulerNonuniqueness.Paper
