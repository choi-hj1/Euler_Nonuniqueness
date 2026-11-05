import EulerNonuniqueness.Section3.IndependentNumeratorRealification
import EulerNonuniqueness.Section3.MovingStrainTangentEquation
import EulerNonuniqueness.Section3.CentroidStrainComplexGauge
import EulerNonuniqueness.Section3.DiskRotatingSecondJet

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group independentRealificationOutputGroup
  independentRealificationInputGroup forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem contourIndependentRealification_generatorAt (data : PeriodicC1HolderHalf)
    (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    contourIndependentRealification (independentDiskRotatingDerivativeAt data pair) =
      fderiv ℝ diskEulerRotatingField data (contourIndependentRealification pair) := by
  let derivative := fderiv ℝ diskEulerRotatingField data
  have commutes := EulerNonuniqueness.General.complexPairReal_extension c1ConjugateCLM
    c1ConjugateCLM_complex_smul c1ConjugateCLM_involution derivative pair
  rw [contourIndependentRealification_eq_twice_real, contourIndependentRealification_eq_twice_real]
  unfold independentDiskRotatingDerivativeAt
  with_reducible_and_instances
    rw [commutes]
    exact (derivative.map_smul (2 : ℝ) _).symm

theorem contourIndependentEmbedding_generatorAt (data direction : PeriodicC1HolderHalf) :
    independentDiskRotatingDerivativeAt data (contourIndependentEmbedding direction) =
      contourIndependentEmbedding (fderiv ℝ diskEulerRotatingField data direction) := by
  let derivative := fderiv ℝ diskEulerRotatingField data
  have identity := EulerNonuniqueness.General.complexPairExtension_embedding c1ConjugateCLM
    c1ConjugateCLM_complex_smul c1ConjugateCLM_involution derivative direction
  unfold independentDiskRotatingDerivativeAt contourIndependentEmbedding
  with_reducible_and_instances
    exact identity

theorem contourIndependentRealification_quadraticAt (data direction : PeriodicC1HolderHalf)
    (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) (coefficient : ℂ) :
    contourIndependentRealification
      (coefficient • contourIndependentQuadraticAt data (contourIndependentEmbedding direction) pair) =
      contourVelocityQuadraticDerivativeCLM data direction
        (contourIndependentRealification (coefficient • pair)) := by
  rw [contourIndependentRealification_eq_twice_real, contourIndependentRealification_eq_twice_real]
  unfold contourIndependentQuadraticAt contourIndependentEmbedding
  with_reducible_and_instances
    exact EulerNonuniqueness.General.complexPairReal_scaled_bilinear_physical_left c1ConjugateCLM
      c1ConjugateCLM_complex_smul c1ConjugateCLM_involution
      (contourVelocityQuadraticDerivativeCLM data) direction pair coefficient

theorem independentCentroidStrainDerivativeAt_physical (data direction : PeriodicC1HolderHalf) :
    independentCentroidStrainDerivativeAt data (contourIndependentEmbedding direction) =
      (fderiv ℝ centroidCenteredStrain data direction, 0) := by
  let derivative := fderiv ℝ centroidCenteredStrain data
  have identity := EulerNonuniqueness.General.complexPairPositiveExtension_embedding c1ConjugateCLM
    c1ConjugateCLM_complex_smul c1ConjugateCLM_involution derivative direction
  unfold independentCentroidStrainDerivativeAt contourIndependentEmbedding
  with_reducible_and_instances
    exact identity

theorem independentCentroidStrainNumeratorAt_realification (data direction : PeriodicC1HolderHalf)
    (primitive : PeriodicC1HolderHalf × PeriodicC1HolderHalf) (coefficient : ℂ) :
    contourIndependentRealification
      (coefficient • independentCentroidStrainNumeratorAt data primitive (contourIndependentEmbedding direction)) =
      coefficient • fderiv ℝ centroidCenteredStrain data direction +
        (2 : ℝ) • contourVelocityQuadraticDerivativeCLM data direction
          (contourIndependentRealification (coefficient • primitive)) := by
  have derivative := independentCentroidStrainDerivativeAt_physical data direction
  unfold independentCentroidStrainNumeratorAt EulerNonuniqueness.General.forcingLinearCoefficient
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.flip_apply, smul_add, map_add]
  rw [derivative]
  have linearTerm : contourIndependentRealification
      (coefficient • (fderiv ℝ centroidCenteredStrain data direction, 0)) =
      coefficient • fderiv ℝ centroidCenteredStrain data direction := by
    change contourIndependentRealification
      (coefficient • fderiv ℝ centroidCenteredStrain data direction,
        coefficient • (0 : PeriodicC1HolderHalf)) = _
    rw [smul_zero, contourIndependentRealification_positive]
  rw [linearTerm]
  have quadratic := contourIndependentRealification_quadraticAt data direction primitive coefficient
  simp only [two_smul ℂ, smul_add, map_add, quadratic, two_smul ℝ]

theorem independentCentroidStrainNumeratorAt_actual_realification (data direction : PeriodicC1HolderHalf)
    (primitive : PeriodicC1HolderHalf × PeriodicC1HolderHalf) (coefficient : ℂ)
    (small : ‖data - standardCircleBanach‖ < min (1 / 3) (min 1 (2 / (3 * Real.pi)))) :
    contourIndependentRealification
      (coefficient • independentCentroidStrainNumeratorAt data primitive (contourIndependentEmbedding direction)) =
      fderiv ℝ (fun current : PeriodicC1HolderHalf => contourCentroidGaugeProjection current
        (coefficient • c1Conjugate current)) data direction +
      fderiv ℝ (fderiv ℝ diskEulerRotatingField) data direction
        (contourIndependentRealification (coefficient • primitive)) := by
  have source := contourCentroidGaugeProjection_complex_strain_fderiv data coefficient (lt_min_iff.mp small).1
  have second := diskEulerRotatingField_second_derivative_apply data direction
    (contourIndependentRealification (coefficient • primitive)) (lt_min_iff.mp small).2
  rw [source, second]
  have scalarValue : (c1ProductCLM (c1Constant coefficient)).comp
      (fderiv ℝ centroidCenteredStrain data) direction =
      coefficient • fderiv ℝ centroidCenteredStrain data direction := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rfl
  rw [scalarValue]
  exact independentCentroidStrainNumeratorAt_realification data direction primitive coefficient

end EulerNonuniqueness.Paper
