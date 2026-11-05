import EulerNonuniqueness.Section3.MovingStrainAffineRemainder
import EulerNonuniqueness.Section3.CentroidStrainRelativeRemainder
import EulerNonuniqueness.General.AffineResidualRelativeRemainder

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

def movingStrainAffineTaylorRemainder (base : PeriodicC1HolderHalf) (coefficient : ℂ)
    (direction : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  projectedComplexStrainTaylorRemainder base coefficient direction +
    (fderiv ℝ diskEulerRotatingField (base + direction) - fderiv ℝ diskEulerRotatingField base -
      fderiv ℝ (fderiv ℝ diskEulerRotatingField) base direction)
        (movingStrainRealPrimitiveValue base coefficient) +
    (fderiv ℝ diskEulerRotatingField (base + direction) - fderiv ℝ diskEulerRotatingField base)
      (movingStrainRealCorrectionCLM base coefficient direction) -
    movingStrainRealCorrectionCLM base coefficient
      (diskEulerRotatingField (base + direction) - diskEulerRotatingField base -
        fderiv ℝ diskEulerRotatingField base direction)

theorem movingStrainAffineResidual_eq_linear_add_taylor
    (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (nearby : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (coefficient : ℂ) (direction : PeriodicC1HolderHalf) :
    movingStrainAffineResidual (fixedRelabelEquivalence angular small standardCircleBanach) coefficient
        (fixedRelabelEquivalence angular small standardCircleBanach + direction) -
      movingStrainAffineLinearResidualCLM (fixedRelabelEquivalence angular small standardCircleBanach)
        coefficient direction =
      movingStrainAffineTaylorRemainder (fixedRelabelEquivalence angular small standardCircleBanach)
        coefficient direction := by
  let base := fixedRelabelEquivalence angular small standardCircleBanach
  let generator := fderiv ℝ diskEulerRotatingField base
  let nextGenerator := fderiv ℝ diskEulerRotatingField (base + direction)
  let second := fderiv ℝ (fderiv ℝ diskEulerRotatingField) base
  let source := fun data : PeriodicC1HolderHalf =>
    contourCentroidGaugeProjection data (coefficient • c1Conjugate data)
  let sourceDerivative := fderiv ℝ source base
  let value := movingStrainRealPrimitiveValue base coefficient
  let partner := movingStrainRealPrimitiveValue base (-Complex.I * coefficient)
  let correction := movingStrainRealCorrectionCLM base coefficient
  let partnerCorrection := movingStrainRealCorrectionCLM base (-Complex.I * coefficient)
  have valueEquation : source base + generator value - partner = 0 := by
    have actual := movingStrainRealPrimitiveValue_actual_equation angular small coefficient nearby
    have equality : partner = source base + generator value := sub_eq_iff_eq_add.mp actual
    rw [equality]
    abel
  have selfZero : diskEulerRotatingField base = 0 := by
    rw [diskEulerRotatingField_fixedRelabel angular small standardCircleBanach
      (by rw [sub_self, norm_zero]; positivity) (lt_min_iff.mp nearby).2,
      diskEulerRotatingField_circle, map_zero]
  have actual := EulerNonuniqueness.General.affineResidual_remainder_identity
    (source base) (source (base + direction)) (diskEulerRotatingField (base + direction))
    (diskEulerRotatingField base) value partner direction generator nextGenerator correction
    partnerCorrection sourceDerivative second valueEquation selfZero
  dsimp only [movingStrainAffineResidual, movingStrainAffineLinearResidualCLM,
    movingStrainAffineTaylorRemainder, projectedComplexStrainTaylorRemainder]
  rw [EulerNonuniqueness.General.affineResidualLinearOperator_apply, add_sub_cancel_left]
  with_reducible_and_instances exact actual

end EulerNonuniqueness.Paper
