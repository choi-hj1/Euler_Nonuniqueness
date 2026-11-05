import EulerNonuniqueness.General.LinearSpectralSolverTransport
import EulerNonuniqueness.Section3.MovingStrainPrimitive

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] actualStrainResonanceC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def fixedRelabelComplexLinearMap (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2) :
    PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexLinearFromReal (fixedRelabelEquivalence angular small).toContinuousLinearMap
    (fixedRelabelEquivalence_complex_smul angular small Complex.I)

def fixedRelabelIndependentComplexLinearMap (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2) :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  (fixedRelabelComplexLinearMap angular small).prodMap (fixedRelabelComplexLinearMap angular small)

theorem fixedRelabelIndependentComplexLinearMap_apply (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    fixedRelabelIndependentComplexLinearMap angular small pair =
      (fixedRelabelEquivalence angular small pair.1, fixedRelabelEquivalence angular small pair.2) := rfl

theorem independentStrainNumerator_circle_identity :
    independentCentroidStrainNumeratorAt standardCircleBanach (independentStrainPrimitiveAt standardCircleBanach) =
      independentForcingLinearCoefficient 0 := by
  rw [independentStrainPrimitiveAt_circle, independentCentroidStrainNumeratorAt_circle]
  unfold actualCentroidStrainLinearCoefficient independentForcingLinearCoefficient
  rw [actualIndependentCentroidStrainDerivative_eq]

theorem independentStrainGenerator_relabel_intertwines (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (composedSmall : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min 1 (2 / (3 * Real.pi))) (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentDiskRotatingDerivativeAt (fixedRelabelEquivalence angular small standardCircleBanach)
        (fixedRelabelIndependentComplexLinearMap angular small pair) =
      fixedRelabelIndependentComplexLinearMap angular small (independentDiskRotatingDerivative pair) := by
  have sourceSmall : ‖standardCircleBanach - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    rw [sub_self, norm_zero]
    positivity
  have identity := independentDiskRotatingDerivativeAt_fixedRelabel angular small standardCircleBanach
    sourceSmall composedSmall pair
  simpa only [fixedRelabelIndependentComplexLinearMap_apply, independentDiskRotatingDerivativeAt_circle] using identity

theorem independentStrainNumerator_relabel_intertwines (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (composedSmall : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi)))) (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentCentroidStrainNumeratorAt (fixedRelabelEquivalence angular small standardCircleBanach)
        (independentStrainPrimitiveAt (fixedRelabelEquivalence angular small standardCircleBanach))
        (fixedRelabelIndependentComplexLinearMap angular small pair) =
      fixedRelabelIndependentComplexLinearMap angular small (independentForcingLinearCoefficient 0 pair) := by
  have sourceSmall : ‖standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))) := by
    rw [sub_self, norm_zero]
    positivity
  have identity := independentCentroidStrainNumeratorAt_fixedRelabel angular small standardCircleBanach
    sourceSmall composedSmall pair (independentStrainPrimitiveAt standardCircleBanach)
  rw [independentStrainNumerator_circle_identity] at identity
  have primitive := independentStrainPrimitiveAt_fixedRelabel angular small standardCircleBanach
  unfold relabeledIndependentPair at primitive
  rw [← primitive]
  simpa only [fixedRelabelIndependentComplexLinearMap_apply] using identity

theorem independentStrainLinearCorrectionAt_relabel_intertwines (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (composedSmall : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi)))) (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentStrainLinearCorrectionAt (fixedRelabelEquivalence angular small standardCircleBanach)
        (fixedRelabelIndependentComplexLinearMap angular small pair) =
      fixedRelabelIndependentComplexLinearMap angular small (independentForcingLinearCorrection 0 pair) := by
  unfold independentStrainLinearCorrectionAt independentDiskSpectralProjectionAt
    independentForcingLinearCorrection independentDiskSpectralProjection
  with_reducible_and_instances
   exact EulerNonuniqueness.General.complexCubicHomologicalSolver_intertwines
    (Space := PeriodicC1HolderHalf × PeriodicC1HolderHalf)
    (fixedRelabelIndependentComplexLinearMap angular small).toLinearMap independentDiskRotatingDerivative
    (independentDiskRotatingDerivativeAt (fixedRelabelEquivalence angular small standardCircleBanach))
    (independentForcingLinearCoefficient 0)
    (independentCentroidStrainNumeratorAt (fixedRelabelEquivalence angular small standardCircleBanach)
      (independentStrainPrimitiveAt (fixedRelabelEquivalence angular small standardCircleBanach)))
    (independentStrainGenerator_relabel_intertwines angular small (lt_min_iff.mp composedSmall).2)
    (independentStrainNumerator_relabel_intertwines angular small composedSmall)
    independentDiskSpectralEigenvalue (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2) pair

end EulerNonuniqueness.Paper
