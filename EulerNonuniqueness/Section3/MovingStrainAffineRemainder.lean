import EulerNonuniqueness.Section3.MovingStrainAffineResidual
import EulerNonuniqueness.Section3.CentroidStrainProjectionJet

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

theorem movingStrainAffineResidual_remainder_of_jet_bounds (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (nearby : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (coefficient : ℂ) (direction : PeriodicC1HolderHalf) {rawConstant centroidConstant : ℝ}
    (rawNonnegative : 0 ≤ rawConstant) (centroidNonnegative : 0 ≤ centroidConstant)
    (directionSmall : ‖direction‖ ≤ 1)
    (nextSmall : ‖fixedRelabelEquivalence angular small standardCircleBanach + direction - standardCircleBanach‖ < 1 / 3)
    (centered : contourCentroidFunctional (fixedRelabelEquivalence angular small standardCircleBanach + direction) =
      contourCentroidFunctional (fixedRelabelEquivalence angular small standardCircleBanach))
    (defect : ‖contourCentroidGaugeProjection (fixedRelabelEquivalence angular small standardCircleBanach) direction - direction‖ ≤
      centroidConstant * ‖direction‖ ^ 2)
    (rawBounds :
      ‖fderiv ℝ (fderiv ℝ diskEulerRotatingField) (fixedRelabelEquivalence angular small standardCircleBanach)‖ ≤ rawConstant ∧
      ‖diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach + direction) -
        diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach) -
        fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach) direction‖ ≤ rawConstant * ‖direction‖ ^ 2 ∧
      ‖fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach + direction) -
        fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach) -
        fderiv ℝ (fderiv ℝ diskEulerRotatingField) (fixedRelabelEquivalence angular small standardCircleBanach) direction‖ ≤ rawConstant * ‖direction‖ ^ 2) :
    ‖movingStrainAffineResidual (fixedRelabelEquivalence angular small standardCircleBanach) coefficient
        (fixedRelabelEquivalence angular small standardCircleBanach + direction) -
      movingStrainAffineLinearResidualCLM (fixedRelabelEquivalence angular small standardCircleBanach) coefficient direction‖ ≤
      (centroidConstant * ‖coefficient‖ + rawConstant *
        ‖movingStrainRealPrimitiveValue (fixedRelabelEquivalence angular small standardCircleBanach) coefficient‖ +
        3 * rawConstant * ‖movingStrainRealCorrectionCLM (fixedRelabelEquivalence angular small standardCircleBanach) coefficient‖) * ‖direction‖ ^ 2 := by
  let base := fixedRelabelEquivalence angular small standardCircleBanach
  let generator := fderiv ℝ diskEulerRotatingField base
  let nextGenerator := fderiv ℝ diskEulerRotatingField (base + direction)
  let second := fderiv ℝ (fderiv ℝ diskEulerRotatingField) base
  let source := fun data : PeriodicC1HolderHalf => contourCentroidGaugeProjection data (coefficient • c1Conjugate data)
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
  have sourceError : ‖source (base + direction) - source base - sourceDerivative direction‖ ≤
      (centroidConstant * ‖coefficient‖) * ‖direction‖ ^ 2 := by
    have actual := (projected_complex_strain_same_centroid_remainder base direction coefficient
      (lt_min_iff.mp nearby).1 nextSmall centered).trans (mul_le_mul_of_nonneg_left defect (norm_nonneg coefficient))
    convert actual using 1 <;> ring
  have secondBound : ‖second direction‖ ≤ rawConstant * ‖direction‖ :=
    (second.le_opNorm direction).trans (mul_le_mul_of_nonneg_right rawBounds.1 (norm_nonneg direction))
  have generatorDifference : ‖nextGenerator - generator‖ ≤ (2 * rawConstant) * ‖direction‖ := by
    have triangle := norm_add_le (nextGenerator - generator - second direction) (second direction)
    rw [sub_add_cancel] at triangle
    have squareBound : rawConstant * ‖direction‖ ^ 2 ≤ rawConstant * ‖direction‖ := by
      exact mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg direction]) rawNonnegative
    exact triangle.trans ((add_le_add rawBounds.2.2 secondBound).trans (by nlinarith))
  have actual := EulerNonuniqueness.General.affineResidual_remainder_bound
    (source base) (source (base + direction)) (diskEulerRotatingField (base + direction))
    (diskEulerRotatingField base) value partner direction generator nextGenerator correction partnerCorrection sourceDerivative second
    (show 0 ≤ 2 * rawConstant by positivity) valueEquation selfZero sourceError rawBounds.2.2 generatorDifference rawBounds.2.1
  have coefficientEquality : centroidConstant * ‖coefficient‖ + rawConstant * ‖value‖ +
      (2 * rawConstant + rawConstant) * ‖correction‖ =
      centroidConstant * ‖coefficient‖ + rawConstant * ‖value‖ + 3 * rawConstant * ‖correction‖ := by ring
  rw [coefficientEquality] at actual
  dsimp only [movingStrainAffineResidual, movingStrainAffineLinearResidualCLM]
  rw [EulerNonuniqueness.General.affineResidualLinearOperator_apply, add_sub_cancel_left]
  with_reducible_and_instances
    exact actual

end EulerNonuniqueness.Paper
