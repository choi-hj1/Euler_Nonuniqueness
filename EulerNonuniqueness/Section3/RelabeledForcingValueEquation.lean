import EulerNonuniqueness.Section3.IndependentStrainFixedRelabel
import EulerNonuniqueness.Section3.RotatingForcingRelabelResidual
import EulerNonuniqueness.Section3.IndependentForcingValueEquation

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance relabeledForcingValueC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def independentDiskRotatingDerivativeAt (data : PeriodicC1HolderHalf) :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexPairExtension c1ConjugateCLM c1ConjugateCLM_complex_smul
    (fderiv ℝ diskEulerRotatingField data)

theorem diskEulerRotatingField_derivative_fixedRelabel (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    (fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular angularSmall data)).comp
        (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap =
      (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap.comp
        (fderiv ℝ diskEulerRotatingField data) := by
  apply EulerNonuniqueness.General.fderiv_linear_equivariant diskEulerRotatingField
    (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap data
    (differentiableAt_diskEulerRotatingField data small)
    (differentiableAt_diskEulerRotatingField _ composedSmall)
  have firstNeighborhood : ∀ᶠ current in 𝓝 data,
      ‖current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    (isOpen_lt ((continuous_id.sub continuous_const).norm) continuous_const).mem_nhds small
  have secondNeighborhood : ∀ᶠ current in 𝓝 data,
      ‖fixedRelabelEquivalence angular angularSmall current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    (isOpen_lt (((fixedRelabelEquivalence angular angularSmall).continuous.sub continuous_const).norm)
      continuous_const).mem_nhds composedSmall
  filter_upwards [firstNeighborhood, secondNeighborhood] with current firstNear secondNear
  exact diskEulerRotatingField_fixedRelabel angular angularSmall current firstNear secondNear

theorem independentDiskRotatingDerivativeAt_fixedRelabel (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (direction : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentDiskRotatingDerivativeAt (fixedRelabelEquivalence angular angularSmall data)
        (fixedRelabelEquivalence angular angularSmall direction.1, fixedRelabelEquivalence angular angularSmall direction.2) =
      (fixedRelabelEquivalence angular angularSmall (independentDiskRotatingDerivativeAt data direction).1,
        fixedRelabelEquivalence angular angularSmall (independentDiskRotatingDerivativeAt data direction).2) := by
  apply EulerNonuniqueness.General.complexPairExtension_linear_relabel c1ConjugateCLM
    (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap c1ConjugateCLM_complex_smul
    (fixedRelabelEquivalence_complex_smul angular angularSmall)
    (fixedRelabelEquivalence_conjugate angular angularSmall)
  intro vector
  exact congrArg (fun derivative : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => derivative vector)
    (diskEulerRotatingField_derivative_fixedRelabel angular angularSmall data small composedSmall)

theorem independentDiskRotatingDerivativeAt_circle :
    independentDiskRotatingDerivativeAt standardCircleBanach = independentDiskRotatingDerivative := by
  unfold independentDiskRotatingDerivativeAt
  rw [diskEulerRotatingField_hasFDerivAt_circle.fderiv]
  rfl

theorem relabeledForcingPrimitiveValue_equation (degree : ℕ) (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall standardCircleBanach - standardCircleBanach‖ <
      min 1 (2 / (3 * Real.pi))) :
    let relabel := fixedRelabelEquivalence angular angularSmall
    let primitive := independentForcingPrimitiveValue degree
    (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) • (relabel primitive.1, relabel primitive.2) -
      independentDiskRotatingDerivativeAt (relabel standardCircleBanach) (relabel primitive.1, relabel primitive.2) =
      (relabel (c1Conjugate (diskCircleMode (degree + 1))), 0) := by
  let relabel := fixedRelabelEquivalence angular angularSmall
  let primitive := independentForcingPrimitiveValue degree
  have sourceSmall : ‖standardCircleBanach - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    rw [sub_self, norm_zero]
    positivity
  have identity := independentDiskRotatingDerivativeAt_fixedRelabel angular angularSmall standardCircleBanach
    sourceSmall composedSmall primitive
  change (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) • (relabel primitive.1, relabel primitive.2) -
      independentDiskRotatingDerivativeAt (relabel standardCircleBanach) (relabel primitive.1, relabel primitive.2) = _
  rw [identity, independentDiskRotatingDerivativeAt_circle]
  have first := congrArg (fun pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf => relabel pair.1)
    (independentForcingPrimitiveValue_equation degree)
  have second := congrArg (fun pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf => relabel pair.2)
    (independentForcingPrimitiveValue_equation degree)
  change relabel ((-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) • primitive.1 -
    (independentDiskRotatingDerivative primitive).1) = relabel (c1Conjugate (diskCircleMode (degree + 1))) at first
  change relabel ((-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) • primitive.2 -
    (independentDiskRotatingDerivative primitive).2) = relabel 0 at second
  simp only [relabel, map_sub, map_zero] at first second
  rw [fixedRelabelEquivalence_complex_smul angular angularSmall] at first second
  exact Prod.ext first second

end EulerNonuniqueness.Paper
