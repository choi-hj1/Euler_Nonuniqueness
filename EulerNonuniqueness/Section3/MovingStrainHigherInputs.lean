import EulerNonuniqueness.Section3.MovingStrainNumeratorRegularity
import EulerNonuniqueness.Section3.ContourVelocityThirdRegularity
import EulerNonuniqueness.General.ComplexPairExtensionRegularity

noncomputable section

open Filter Metric
open scoped Topology

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

local instance movingStrainHigherInputsC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem independentDiskRotatingDerivativeAt_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear independentDiskRotatingDerivativeAt standardCircleBanach := by
  let rotation := c1ProductCLM (c1Constant (Complex.I / 2))
  let extension := EulerNonuniqueness.General.complexPairExtension c1ConjugateCLM c1ConjugateCLM_complex_smul
  have inner := contourVelocity_derivative_hasLipschitzDerivativeNear.sub
    (EulerNonuniqueness.General.hasLipschitzDerivativeNear_const rotation standardCircleBanach)
  have outer := EulerNonuniqueness.General.complexPairExtension_hasLipschitzDerivativeNear
    c1ConjugateCLM c1ConjugateCLM_complex_smul (fderiv ℝ extendedContourVelocity standardCircleBanach - rotation)
  have actual : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun current => extension (fderiv ℝ extendedContourVelocity current - rotation)) standardCircleBanach :=
    EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp
      (outer := extension) (inner := fun current => fderiv ℝ extendedContourVelocity current - rotation) outer inner
  apply actual.congr
  have thresholdPositive : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  filter_upwards [ball_mem_nhds standardCircleBanach thresholdPositive] with current member
  have small : ‖current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    simpa only [mem_ball, dist_eq_norm] using member
  have rotationJet : HasFDerivAt (c1Product (c1Constant (Complex.I / 2))) rotation current :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) rotation
  have fieldJet := (differentiableAt_extendedContourVelocity current small).hasFDerivAt.sub rotationJet
  have identity : fderiv ℝ diskEulerRotatingField current = fderiv ℝ extendedContourVelocity current - rotation :=
    fieldJet.fderiv
  change extension (fderiv ℝ diskEulerRotatingField current) = extension (fderiv ℝ extendedContourVelocity current - rotation)
  rw [identity]

theorem independentCentroidStrainDerivativeAt_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear independentCentroidStrainDerivativeAt standardCircleBanach := by
  have small : ‖standardCircleBanach - standardCircleBanach‖ < (1 / 3 : ℝ) := by norm_num
  have inner : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fderiv ℝ centroidCenteredStrain) standardCircleBanach :=
    EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt
      (centroidCenteredStrain_analyticAt standardCircleBanach small).fderiv
  have outer := EulerNonuniqueness.General.complexPairPositiveExtension_hasLipschitzDerivativeNear
    c1ConjugateCLM c1ConjugateCLM_complex_smul (fderiv ℝ centroidCenteredStrain standardCircleBanach)
  exact EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp
    (outer := EulerNonuniqueness.General.complexPairPositiveExtension c1ConjugateCLM c1ConjugateCLM_complex_smul)
    (inner := fderiv ℝ centroidCenteredStrain) outer inner

theorem independentStrainPrimitiveAt_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear independentStrainPrimitiveAt standardCircleBanach := by
  let primitiveMap : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
    ((c1ProductCLM (c1Constant (diskForcingPrimitiveFactor 0 1))).comp c1ConjugateCLM).prod 0
  have identity : (primitiveMap : PeriodicC1HolderHalf → PeriodicC1HolderHalf × PeriodicC1HolderHalf) =
      independentStrainPrimitiveAt := by
    funext data
    apply Prod.ext
    · apply PeriodicC1HolderHalf.ext_value
      intro label
      rfl
    · rfl
  rw [← identity]
  exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_continuousLinearMap primitiveMap standardCircleBanach

theorem contourIndependentQuadraticAt_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear contourIndependentQuadraticAt standardCircleBanach := by
  have third := contourVelocity_derivative_hasLipschitzSecondDerivativeNear
  unfold EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear at third
  have rawRegular := third.2
  let halfMap : (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) →L[ℝ]
      (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
    (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ _
  have outerHalf := EulerNonuniqueness.General.hasLipschitzDerivativeNear_continuousLinearMap halfMap
    (fderiv ℝ (fderiv ℝ extendedContourVelocity) standardCircleBanach)
  have quadraticRegular : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      contourVelocityQuadraticDerivativeCLM standardCircleBanach := by
    unfold contourVelocityQuadraticDerivativeCLM
    exact EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp
      (outer := fun bilinear => halfMap bilinear)
      (inner := fderiv ℝ (fderiv ℝ extendedContourVelocity)) outerHalf rawRegular
  have outer := EulerNonuniqueness.General.complexPairBilinearExtension_hasLipschitzDerivativeNear
    c1ConjugateCLM c1ConjugateCLM_complex_smul (contourVelocityQuadraticDerivativeCLM standardCircleBanach)
  unfold contourIndependentQuadraticAt
  exact EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp
    (outer := EulerNonuniqueness.General.complexPairBilinearExtension c1ConjugateCLM c1ConjugateCLM_complex_smul)
    (inner := contourVelocityQuadraticDerivativeCLM) outer quadraticRegular

end EulerNonuniqueness.Paper
