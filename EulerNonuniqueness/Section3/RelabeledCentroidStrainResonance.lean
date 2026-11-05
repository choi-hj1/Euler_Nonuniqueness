import EulerNonuniqueness.Section3.IndependentStrainFixedRelabel

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] actualStrainResonanceC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def relabeledIndependentPair (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) : PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  (fixedRelabelEquivalence angular small pair.1, fixedRelabelEquivalence angular small pair.2)

def inverseRelabeledIndependentPair (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) : PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  ((fixedRelabelEquivalence angular small).symm pair.1, (fixedRelabelEquivalence angular small).symm pair.2)

theorem inverseRelabeledIndependentPair_apply (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    inverseRelabeledIndependentPair angular small (relabeledIndependentPair angular small pair) = pair := by
  exact Prod.ext ((fixedRelabelEquivalence angular small).symm_apply_apply pair.1)
    ((fixedRelabelEquivalence angular small).symm_apply_apply pair.2)

theorem relabeledCentroidStrainNumerator_pullback (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (direction : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    inverseRelabeledIndependentPair angular angularSmall
      (independentCentroidStrainNumeratorAt (fixedRelabelEquivalence angular angularSmall standardCircleBanach)
        (relabeledIndependentPair angular angularSmall (independentForcingPrimitiveValue 0))
        (relabeledIndependentPair angular angularSmall direction)) = actualCentroidStrainLinearCoefficient direction := by
  have sourceSmall : ‖standardCircleBanach - standardCircleBanach‖ < min (1 / 3) (min 1 (2 / (3 * Real.pi))) := by
    rw [sub_self, norm_zero]
    positivity
  have identity := independentCentroidStrainNumeratorAt_fixedRelabel angular angularSmall standardCircleBanach
    sourceSmall composedSmall direction (independentForcingPrimitiveValue 0)
  change independentCentroidStrainNumeratorAt _
      (relabeledIndependentPair angular angularSmall (independentForcingPrimitiveValue 0))
      (relabeledIndependentPair angular angularSmall direction) =
    relabeledIndependentPair angular angularSmall
      (independentCentroidStrainNumeratorAt standardCircleBanach (independentForcingPrimitiveValue 0) direction) at identity
  rw [identity, inverseRelabeledIndependentPair_apply, independentCentroidStrainNumeratorAt_circle]

def relabeledCentroidStrainFirstRadialBlock (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (radial : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  independentNegativeRadial (inverseRelabeledIndependentPair angular small
    (independentCentroidStrainNumeratorAt (fixedRelabelEquivalence angular small standardCircleBanach)
      (relabeledIndependentPair angular small (independentForcingPrimitiveValue 0))
      (relabeledIndependentPair angular small (independentPositiveMaterial radial))))

theorem relabeledCentroidStrainFirstRadialBlock_eq (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi)))) (radial : PeriodicC1HolderHalf) :
    relabeledCentroidStrainFirstRadialBlock angular angularSmall radial = actualCentroidStrainRadialBlock radial := by
  unfold relabeledCentroidStrainFirstRadialBlock
  rw [relabeledCentroidStrainNumerator_pullback angular angularSmall composedSmall]
  rfl

end EulerNonuniqueness.Paper
