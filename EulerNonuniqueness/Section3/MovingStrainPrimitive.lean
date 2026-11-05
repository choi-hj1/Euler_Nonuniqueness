import EulerNonuniqueness.Section3.MovingStrainSpectralCorrection
import EulerNonuniqueness.Section3.RelabeledCentroidStrainResonance

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] actualStrainResonanceC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem strainDiskCircleMode_one : diskCircleMode (0 + 1) = standardCircleBanach := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [diskCircleMode_value, pow_one]
  rfl

theorem independentStrainPrimitiveAt_circle :
    independentStrainPrimitiveAt standardCircleBanach = independentForcingPrimitiveValue 0 := by
  unfold independentStrainPrimitiveAt independentForcingPrimitiveValue
  rw [strainDiskCircleMode_one]

theorem independentStrainPrimitiveAt_fixedRelabel (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf) :
    relabeledIndependentPair angular small (independentStrainPrimitiveAt data) =
      independentStrainPrimitiveAt (fixedRelabelEquivalence angular small data) := by
  apply Prod.ext
  · change fixedRelabelEquivalence angular small (diskForcingPrimitiveFactor 0 1 • c1Conjugate data) = _
    rw [fixedRelabelEquivalence_complex_smul]
    congr 1
    exact (fixedRelabelEquivalence_conjugate angular small data).symm
  · exact (fixedRelabelEquivalence angular small).map_zero

theorem independentStrainPrimitiveAt_relabeled_equation (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (composedSmall : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min 1 (2 / (3 * Real.pi))) :
    (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2) •
        independentStrainPrimitiveAt (fixedRelabelEquivalence angular small standardCircleBanach) -
      independentDiskRotatingDerivativeAt (fixedRelabelEquivalence angular small standardCircleBanach)
        (independentStrainPrimitiveAt (fixedRelabelEquivalence angular small standardCircleBanach)) =
      (c1Conjugate (fixedRelabelEquivalence angular small standardCircleBanach), 0) := by
  have equation := relabeledForcingPrimitiveValue_equation 0 angular small composedSmall
  change (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2) •
      relabeledIndependentPair angular small (independentForcingPrimitiveValue 0) -
      independentDiskRotatingDerivativeAt (fixedRelabelEquivalence angular small standardCircleBanach)
        (relabeledIndependentPair angular small (independentForcingPrimitiveValue 0)) = _ at equation
  rw [← independentStrainPrimitiveAt_circle, independentStrainPrimitiveAt_fixedRelabel] at equation
  rw [strainDiskCircleMode_one] at equation
  have source := fixedRelabelEquivalence_conjugate angular small standardCircleBanach
  exact equation.trans (congrArg (fun data : PeriodicC1HolderHalf => (data, (0 : PeriodicC1HolderHalf))) source.symm)

end EulerNonuniqueness.Paper
