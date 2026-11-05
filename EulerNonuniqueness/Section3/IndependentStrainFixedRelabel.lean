import EulerNonuniqueness.Section3.CentroidStrainFixedRelabel
import EulerNonuniqueness.Section3.FixedRelabelForcingJets
import EulerNonuniqueness.Section3.ActualCentroidStrainResonance
import EulerNonuniqueness.General.ComplexPairRelabel

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance independentStrainRelabelC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem fixedRelabelEquivalence_conjugate (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (data : PeriodicC1HolderHalf) :
    c1ConjugateCLM (fixedRelabelEquivalence angular small data) =
      fixedRelabelEquivalence angular small (c1ConjugateCLM data) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

def contourIndependentQuadraticAt (data : PeriodicC1HolderHalf) :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
      (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexPairBilinearExtension c1ConjugateCLM c1ConjugateCLM_complex_smul
    (contourVelocityQuadraticDerivativeCLM data)

def independentCentroidStrainDerivativeAt (data : PeriodicC1HolderHalf) :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexPairPositiveExtension c1ConjugateCLM c1ConjugateCLM_complex_smul
    (fderiv ℝ centroidCenteredStrain data)

def independentCentroidStrainNumeratorAt (data : PeriodicC1HolderHalf)
    (primitive : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.forcingLinearCoefficient (independentCentroidStrainDerivativeAt data)
    (contourIndependentQuadraticAt data) primitive

theorem independentCentroidStrainDerivativeAt_fixedRelabel (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ < 1 / 3)
    (direction : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentCentroidStrainDerivativeAt (fixedRelabelEquivalence angular angularSmall data)
        (fixedRelabelEquivalence angular angularSmall direction.1, fixedRelabelEquivalence angular angularSmall direction.2) =
      (fixedRelabelEquivalence angular angularSmall (independentCentroidStrainDerivativeAt data direction).1,
        fixedRelabelEquivalence angular angularSmall (independentCentroidStrainDerivativeAt data direction).2) := by
  apply EulerNonuniqueness.General.complexPairPositiveExtension_linear_relabel c1ConjugateCLM
    (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap c1ConjugateCLM_complex_smul
    (fixedRelabelEquivalence_complex_smul angular angularSmall)
    (fixedRelabelEquivalence_conjugate angular angularSmall)
  intro vector
  exact congrArg (fun derivative : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => derivative vector)
    (centroidCenteredStrain_derivative_fixedRelabel angular angularSmall data small composedSmall)

theorem contourIndependentQuadraticAt_fixedRelabel (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (first second : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    contourIndependentQuadraticAt (fixedRelabelEquivalence angular angularSmall data)
        (fixedRelabelEquivalence angular angularSmall first.1, fixedRelabelEquivalence angular angularSmall first.2)
        (fixedRelabelEquivalence angular angularSmall second.1, fixedRelabelEquivalence angular angularSmall second.2) =
      (fixedRelabelEquivalence angular angularSmall (contourIndependentQuadraticAt data first second).1,
        fixedRelabelEquivalence angular angularSmall (contourIndependentQuadraticAt data first second).2) := by
  apply EulerNonuniqueness.General.complexPairBilinearExtension_linear_relabel c1ConjugateCLM
    (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap c1ConjugateCLM_complex_smul
    (fixedRelabelEquivalence_complex_smul angular angularSmall)
    (fixedRelabelEquivalence_conjugate angular angularSmall)
  intro firstDirection secondDirection
  change (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ extendedContourVelocity)
      (fixedRelabelEquivalence angular angularSmall data)
      (fixedRelabelEquivalence angular angularSmall firstDirection)
      (fixedRelabelEquivalence angular angularSmall secondDirection) =
    fixedRelabelEquivalence angular angularSmall
      ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ extendedContourVelocity) data firstDirection secondDirection)
  rw [contourVelocity_hessian_fixedRelabel angular angularSmall data firstDirection secondDirection small composedSmall,
    map_smul]

theorem fixedRelabel_pair_add_smul (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (scalar : ℂ) (first second : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    (fixedRelabelEquivalence angular small first.1, fixedRelabelEquivalence angular small first.2) +
        scalar • (fixedRelabelEquivalence angular small second.1, fixedRelabelEquivalence angular small second.2) =
      (fixedRelabelEquivalence angular small (first + scalar • second).1,
        fixedRelabelEquivalence angular small (first + scalar • second).2) := by
  apply Prod.ext
  · change fixedRelabelEquivalence angular small first.1 + scalar • fixedRelabelEquivalence angular small second.1 =
      fixedRelabelEquivalence angular small (first.1 + scalar • second.1)
    rw [map_add, fixedRelabelEquivalence_complex_smul]
  · change fixedRelabelEquivalence angular small first.2 + scalar • fixedRelabelEquivalence angular small second.2 =
      fixedRelabelEquivalence angular small (first.2 + scalar • second.2)
    rw [map_add, fixedRelabelEquivalence_complex_smul]

theorem independentCentroidStrainNumeratorAt_fixedRelabel (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (direction primitive : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentCentroidStrainNumeratorAt (fixedRelabelEquivalence angular angularSmall data)
        (fixedRelabelEquivalence angular angularSmall primitive.1, fixedRelabelEquivalence angular angularSmall primitive.2)
        (fixedRelabelEquivalence angular angularSmall direction.1, fixedRelabelEquivalence angular angularSmall direction.2) =
      (fixedRelabelEquivalence angular angularSmall (independentCentroidStrainNumeratorAt data primitive direction).1,
        fixedRelabelEquivalence angular angularSmall (independentCentroidStrainNumeratorAt data primitive direction).2) := by
  simp only [independentCentroidStrainNumeratorAt, EulerNonuniqueness.General.forcingLinearCoefficient,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.flip_apply]
  rw [independentCentroidStrainDerivativeAt_fixedRelabel angular angularSmall data
      (lt_min_iff.mp small).1 (lt_min_iff.mp composedSmall).1,
    contourIndependentQuadraticAt_fixedRelabel angular angularSmall data
      (lt_min_iff.mp small).2 (lt_min_iff.mp composedSmall).2]
  exact fixedRelabel_pair_add_smul angular angularSmall 2
    (independentCentroidStrainDerivativeAt data direction) (contourIndependentQuadraticAt data direction primitive)

theorem independentCentroidStrainNumeratorAt_circle :
    independentCentroidStrainNumeratorAt standardCircleBanach (independentForcingPrimitiveValue 0) =
      actualCentroidStrainLinearCoefficient := rfl

end EulerNonuniqueness.Paper
