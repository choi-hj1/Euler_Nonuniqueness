import EulerNonuniqueness.General.ContinuousHomologicalTransport
import EulerNonuniqueness.Section3.MovingStrainSolverTransport
import EulerNonuniqueness.Section3.CircleForcingHomologicalEquation
import EulerNonuniqueness.Section3.FixedRelabelCentroidPullback
import EulerNonuniqueness.Section3.FixedRelabelContinuousVectors

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentTangentEquationC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem fixedRelabelIndependentComplexLinearMap_embedding (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (direction : PeriodicC1HolderHalf) :
    fixedRelabelIndependentComplexLinearMap angular small (contourIndependentEmbedding direction) =
      contourIndependentEmbedding (fixedRelabelEquivalence angular small direction) := by
  apply Prod.ext
  · rfl
  · exact (fixedRelabelEquivalence_conjugate angular small direction).symm

theorem independentStrainLinearCorrectionAt_transported_tangent_equation (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (composedSmall : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule)
    (centered : fderiv ℝ contourCentroidFunctional standardCircleBanach direction = 0) :
    EulerNonuniqueness.General.linearHomologicalOperator
      (independentDiskRotatingDerivativeAt (fixedRelabelEquivalence angular small standardCircleBanach))
      (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2)
      (independentStrainLinearCorrectionAt (fixedRelabelEquivalence angular small standardCircleBanach))
      (fixedRelabelIndependentComplexLinearMap angular small (contourIndependentEmbedding direction)) =
    independentCentroidStrainNumeratorAt (fixedRelabelEquivalence angular small standardCircleBanach)
      (independentStrainPrimitiveAt (fixedRelabelEquivalence angular small standardCircleBanach))
      (fixedRelabelIndependentComplexLinearMap angular small (contourIndependentEmbedding direction)) := by
  have correctionTransport : ∀ vector : PeriodicC1HolderHalf × PeriodicC1HolderHalf,
      independentStrainLinearCorrectionAt (fixedRelabelEquivalence angular small standardCircleBanach)
        (fixedRelabelIndependentComplexLinearMap angular small vector) =
      fixedRelabelIndependentComplexLinearMap angular small (independentForcingLinearCorrection 0 vector) := by
    intro vector
    with_reducible_and_instances
      exact independentStrainLinearCorrectionAt_relabel_intertwines angular small composedSmall vector
  have generatorTransport : ∀ vector : PeriodicC1HolderHalf × PeriodicC1HolderHalf,
      independentDiskRotatingDerivativeAt (fixedRelabelEquivalence angular small standardCircleBanach)
        (fixedRelabelIndependentComplexLinearMap angular small vector) =
      fixedRelabelIndependentComplexLinearMap angular small (independentDiskRotatingDerivative vector) := by
    intro vector
    with_reducible_and_instances
      exact independentStrainGenerator_relabel_intertwines angular small (lt_min_iff.mp composedSmall).2 vector
  have transported : EulerNonuniqueness.General.linearHomologicalOperator
      (independentDiskRotatingDerivativeAt (fixedRelabelEquivalence angular small standardCircleBanach))
      (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2)
      (independentStrainLinearCorrectionAt (fixedRelabelEquivalence angular small standardCircleBanach))
      (fixedRelabelIndependentComplexLinearMap angular small (contourIndependentEmbedding direction)) =
    fixedRelabelIndependentComplexLinearMap angular small
      (EulerNonuniqueness.General.linearHomologicalOperator independentDiskRotatingDerivative
        (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2) (independentForcingLinearCorrection 0)
        (contourIndependentEmbedding direction)) := by
   with_reducible_and_instances
    exact EulerNonuniqueness.General.linearHomologicalOperator_intertwines_continuous
      (Space := PeriodicC1HolderHalf × PeriodicC1HolderHalf)
      (fixedRelabelIndependentComplexLinearMap angular small) independentDiskRotatingDerivative
      (independentDiskRotatingDerivativeAt (fixedRelabelEquivalence angular small standardCircleBanach))
      (independentForcingLinearCorrection 0)
      (independentStrainLinearCorrectionAt (fixedRelabelEquivalence angular small standardCircleBanach))
      generatorTransport correctionTransport
      (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2) (contourIndependentEmbedding direction)
  have sourceEquation := independentForcingLinearCorrection_operator_tangent_equation 0 direction member centered
  exact transported.trans
    ((congrArg (fixedRelabelIndependentComplexLinearMap angular small) sourceEquation).trans
      (independentStrainNumerator_relabel_intertwines angular small composedSmall
        (contourIndependentEmbedding direction)).symm)

theorem independentStrainLinearCorrectionAt_tangent_equation (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (angularMember : angular ∈ contourContinuousVectorSubmodule)
    (composedSmall : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule)
    (centered : fderiv ℝ contourCentroidFunctional
      (fixedRelabelEquivalence angular small standardCircleBanach) direction = 0) :
    EulerNonuniqueness.General.linearHomologicalOperator
      (independentDiskRotatingDerivativeAt (fixedRelabelEquivalence angular small standardCircleBanach))
      (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2)
      (independentStrainLinearCorrectionAt (fixedRelabelEquivalence angular small standardCircleBanach))
      (contourIndependentEmbedding direction) =
    independentCentroidStrainNumeratorAt (fixedRelabelEquivalence angular small standardCircleBanach)
      (independentStrainPrimitiveAt (fixedRelabelEquivalence angular small standardCircleBanach))
      (contourIndependentEmbedding direction) := by
  let sourceDirection := (fixedRelabelEquivalence angular small).symm direction
  have sourceMember : sourceDirection ∈ contourContinuousVectorSubmodule :=
    fixedRelabelEquivalence_symm_mem_continuousVector angular small angularMember direction member
  have sourceSmall : ‖standardCircleBanach - standardCircleBanach‖ < (1 / 3 : ℝ) := by norm_num
  have sourceCentered : fderiv ℝ contourCentroidFunctional standardCircleBanach sourceDirection = 0 :=
    (contourCentroidFunctional_derivative_pullback angular small standardCircleBanach direction
      sourceSmall (lt_min_iff.mp composedSmall).1).trans centered
  have targetEquation := independentStrainLinearCorrectionAt_transported_tangent_equation angular small composedSmall
    sourceDirection sourceMember sourceCentered
  simpa only [ContinuousLinearMap.coe_coe, fixedRelabelIndependentComplexLinearMap_embedding,
    sourceDirection, ContinuousLinearEquiv.apply_symm_apply] using targetEquation

end EulerNonuniqueness.Paper
