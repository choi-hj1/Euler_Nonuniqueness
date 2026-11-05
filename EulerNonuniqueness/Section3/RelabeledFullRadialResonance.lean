import EulerNonuniqueness.Section3.RelabeledCentroidStrainResonance
import EulerNonuniqueness.Section3.IndependentFullRadialResonance
import EulerNonuniqueness.Section3.FixedRelabelCentroidPullback
import EulerNonuniqueness.Section3.FixedRelabelContinuousVectors

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentFullRadialC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def relabeledCentroidStrainFullRadialBlock (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (radial : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  independentFullRadial (inverseRelabeledIndependentPair angular small
    (independentCentroidStrainNumeratorAt (fixedRelabelEquivalence angular small standardCircleBanach)
      (relabeledIndependentPair angular small (independentForcingPrimitiveValue 0))
      (relabeledIndependentPair angular small (independentPositiveMaterial radial))))

theorem relabeledCentroidStrainFullRadialBlock_eq (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi)))) (radial : PeriodicC1HolderHalf) :
    relabeledCentroidStrainFullRadialBlock angular angularSmall radial = actualCentroidStrainFullRadialBlock radial := by
  unfold relabeledCentroidStrainFullRadialBlock
  rw [relabeledCentroidStrainNumerator_pullback angular angularSmall composedSmall]
  simp only [actualCentroidStrainFullRadialBlock, EulerNonuniqueness.General.weightedOperatorBlock,
    ContinuousLinearMap.comp_apply]

theorem relabeledCentroidStrain_full_radial_tangent_resonance_zero (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (direction : PeriodicC1HolderHalf)
    (member : (fixedRelabelEquivalence angular angularSmall).symm direction ∈ contourContinuousVectorSubmodule)
    (centered : fderiv ℝ contourCentroidFunctional
      (fixedRelabelEquivalence angular angularSmall standardCircleBanach) direction = 0) :
    periodicHilbertNegativeProjection
      (relabeledCentroidStrainFullRadialBlock angular angularSmall
        (periodicHilbertPositiveProjection (diskRadialPart ((fixedRelabelEquivalence angular angularSmall).symm direction)))) = 0 := by
  rw [relabeledCentroidStrainFullRadialBlock_eq angular angularSmall composedSmall]
  have sourceSmall : ‖standardCircleBanach - standardCircleBanach‖ < 1 / 3 := by
    rw [sub_self, norm_zero]
    norm_num
  have sourceCentered : fderiv ℝ contourCentroidFunctional standardCircleBanach
      ((fixedRelabelEquivalence angular angularSmall).symm direction) = 0 := by
    exact (contourCentroidFunctional_derivative_pullback angular angularSmall standardCircleBanach direction
      sourceSmall (lt_min_iff.mp composedSmall).1).trans centered
  exact actualCentroidStrain_full_radial_tangent_resonance_zero
    ((fixedRelabelEquivalence angular angularSmall).symm direction) member sourceCentered

theorem relabeledCentroidStrain_full_radial_actual_tangent_resonance_zero (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (angularMember : angular ∈ contourContinuousVectorSubmodule)
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule)
    (centered : fderiv ℝ contourCentroidFunctional
      (fixedRelabelEquivalence angular angularSmall standardCircleBanach) direction = 0) :
    periodicHilbertNegativeProjection
      (relabeledCentroidStrainFullRadialBlock angular angularSmall
        (periodicHilbertPositiveProjection (diskRadialPart ((fixedRelabelEquivalence angular angularSmall).symm direction)))) = 0 := by
  exact relabeledCentroidStrain_full_radial_tangent_resonance_zero angular angularSmall composedSmall direction
    (fixedRelabelEquivalence_symm_mem_continuousVector angular angularSmall angularMember direction member) centered

end EulerNonuniqueness.Paper
