import EulerNonuniqueness.Section3.MovingForcingRealification
import EulerNonuniqueness.Section3.MovingStrainRealCorrection
import EulerNonuniqueness.General.RealifiedHomologicalEquation

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

theorem projected_complex_strain_relabel_value (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (coefficient : ℂ)
    (nearby : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ < 1 / 3) :
    contourCentroidGaugeProjection (fixedRelabelEquivalence angular small standardCircleBanach)
      (coefficient • c1Conjugate (fixedRelabelEquivalence angular small standardCircleBanach)) =
      coefficient • c1Conjugate (fixedRelabelEquivalence angular small standardCircleBanach) := by
  rw [contourCentroidGaugeProjection_complex_strain _ coefficient nearby]
  have centered : contourCentroidFunctional (fixedRelabelEquivalence angular small standardCircleBanach) = 0 :=
    (contourCentroidFunctional_fixedRelabel angular small standardCircleBanach).trans
      contourCentroidFunctional_standardCircle_zero
  congr 1
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change star ((fixedRelabelEquivalence angular small standardCircleBanach).val.1 label) -
    star (contourCentroidFunctional (fixedRelabelEquivalence angular small standardCircleBanach)) = _
  rw [centered, star_zero, sub_zero]
  rfl

theorem movingStrainRealPrimitiveValue_actual_equation (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (coefficient : ℂ)
    (nearby : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi)))) :
    movingStrainRealPrimitiveValue (fixedRelabelEquivalence angular small standardCircleBanach) (-Complex.I * coefficient) -
      fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach)
        (movingStrainRealPrimitiveValue (fixedRelabelEquivalence angular small standardCircleBanach) coefficient) =
      contourCentroidGaugeProjection (fixedRelabelEquivalence angular small standardCircleBanach)
        (coefficient • c1Conjugate (fixedRelabelEquivalence angular small standardCircleBanach)) := by
  let data := fixedRelabelEquivalence angular small standardCircleBanach
  have pairEquation := independentStrainPrimitiveAt_relabeled_equation angular small (lt_min_iff.mp nearby).2
  have equation := congrArg (fun pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf =>
    contourIndependentRealification (coefficient • pair)) pairEquation
  simp only [smul_sub, map_sub, smul_smul] at equation
  have frequency : coefficient * (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2) = -Complex.I * coefficient := by
    norm_num
    ring
  rw [frequency] at equation
  have generator : contourIndependentRealification
      (coefficient • independentDiskRotatingDerivativeAt data (independentStrainPrimitiveAt data)) =
      fderiv ℝ diskEulerRotatingField data
        (contourIndependentRealification (coefficient • independentStrainPrimitiveAt data)) := by
    rw [← (independentDiskRotatingDerivativeAt data).map_smul coefficient,
      contourIndependentRealification_generatorAt]
  have source : contourIndependentRealification (coefficient • (c1Conjugate data, 0)) =
      coefficient • c1Conjugate data := by
    change contourIndependentRealification (coefficient • c1Conjugate data, coefficient • (0 : PeriodicC1HolderHalf)) = _
    rw [smul_zero, contourIndependentRealification_positive]
  rw [generator, source, ← projected_complex_strain_relabel_value angular small coefficient (lt_min_iff.mp nearby).1] at equation
  exact equation

theorem movingStrainRealCorrectionCLM_actual_tangent_equation (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (angularMember : angular ∈ contourContinuousVectorSubmodule)
    (nearby : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (coefficient : ℂ) (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule)
    (centered : fderiv ℝ contourCentroidFunctional
      (fixedRelabelEquivalence angular small standardCircleBanach) direction = 0) :
    movingStrainRealCorrectionCLM (fixedRelabelEquivalence angular small standardCircleBanach) (-Complex.I * coefficient) direction +
      movingStrainRealCorrectionCLM (fixedRelabelEquivalence angular small standardCircleBanach) coefficient
        (fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach) direction) -
      fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach)
        (movingStrainRealCorrectionCLM (fixedRelabelEquivalence angular small standardCircleBanach) coefficient direction) =
      fderiv ℝ (fun current : PeriodicC1HolderHalf => contourCentroidGaugeProjection current
        (coefficient • c1Conjugate current)) (fixedRelabelEquivalence angular small standardCircleBanach) direction +
      fderiv ℝ (fderiv ℝ diskEulerRotatingField) (fixedRelabelEquivalence angular small standardCircleBanach) direction
        (movingStrainRealPrimitiveValue (fixedRelabelEquivalence angular small standardCircleBanach) coefficient) := by
  let data := fixedRelabelEquivalence angular small standardCircleBanach
  have pairEquation := independentStrainLinearCorrectionAt_tangent_equation angular small angularMember nearby direction member centered
  simp only [EulerNonuniqueness.General.linearHomologicalOperator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply] at pairEquation
  let complexGenerator := independentDiskRotatingDerivativeAt data
  let correction := independentStrainLinearCorrectionAt data
  let realGenerator := fderiv ℝ diskEulerRotatingField data
  let numerator := independentCentroidStrainNumeratorAt data (independentStrainPrimitiveAt data)
    (contourIndependentEmbedding direction)
  have equation : EulerNonuniqueness.General.realifiedComplexOperator contourIndependentRealification
      contourIndependentEmbedding correction (coefficient * (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2)) direction +
      EulerNonuniqueness.General.realifiedComplexOperator contourIndependentRealification
        contourIndependentEmbedding correction coefficient (realGenerator direction) -
      realGenerator (EulerNonuniqueness.General.realifiedComplexOperator contourIndependentRealification
        contourIndependentEmbedding correction coefficient direction) = contourIndependentRealification (coefficient • numerator) := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.realified_homological_equation
        contourIndependentRealification contourIndependentEmbedding complexGenerator correction realGenerator
        (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2) coefficient direction numerator
        (contourIndependentEmbedding_generatorAt data direction)
        (contourIndependentRealification_generatorAt data) pairEquation
  have frequency : coefficient * (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2) = -Complex.I * coefficient := by
    norm_num
    ring
  rw [frequency] at equation
  have actualNumerator := independentCentroidStrainNumeratorAt_actual_realification data direction
    (independentStrainPrimitiveAt data) coefficient nearby
  dsimp only [movingStrainRealCorrectionCLM, movingStrainRealPrimitiveValue]
  dsimp only [correction, realGenerator, numerator] at equation
  with_reducible_and_instances
    exact equation.trans actualNumerator

end EulerNonuniqueness.Paper
