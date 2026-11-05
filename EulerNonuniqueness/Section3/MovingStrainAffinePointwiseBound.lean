import EulerNonuniqueness.Section3.MovingStrainAffineRemainder
import EulerNonuniqueness.Section3.MovingStrainAffineLinearBounds
import EulerNonuniqueness.Section3.MovingStrainPrimitiveFormula
import EulerNonuniqueness.Section3.MovingStrainRealUniform
import EulerNonuniqueness.General.AffineResidualScaleBound

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule

def movingStrainAffineBoundConstant (raw gauge correction centroid : ℝ) : ℝ :=
  centroid + 6 * raw + 3 * raw * correction +
    (gauge + 6 * raw + 2 * raw * correction + correction) * centroid

theorem movingStrainAffineResidual_pointwise_quadratic_bound (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (angularMember : angular ∈ contourContinuousVectorSubmodule)
    (nearby : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (coefficient : ℂ) (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule)
    {rawConstant gaugeConstant correctionConstant centroidConstant : ℝ}
    (rawNonnegative : 0 ≤ rawConstant) (gaugeNonnegative : 0 ≤ gaugeConstant)
    (correctionNonnegative : 0 ≤ correctionConstant) (centroidNonnegative : 0 ≤ centroidConstant)
    (directionSmall : ‖direction‖ ≤ 1)
    (baseBound : ‖fixedRelabelEquivalence angular small standardCircleBanach‖ ≤ 3)
    (nextSmall : ‖fixedRelabelEquivalence angular small standardCircleBanach + direction - standardCircleBanach‖ < 1 / 3)
    (centered : contourCentroidFunctional (fixedRelabelEquivalence angular small standardCircleBanach + direction) =
      contourCentroidFunctional (fixedRelabelEquivalence angular small standardCircleBanach))
    (gaugeBound : ‖contourCentroidGaugeProjection (fixedRelabelEquivalence angular small standardCircleBanach)‖ ≤ gaugeConstant)
    (correctionBound : ‖movingStrainRealCorrectionCLM (fixedRelabelEquivalence angular small standardCircleBanach) coefficient‖ ≤ correctionConstant * ‖coefficient‖)
    (partnerBound : ‖movingStrainRealCorrectionCLM (fixedRelabelEquivalence angular small standardCircleBanach) (-Complex.I * coefficient)‖ ≤ correctionConstant * ‖coefficient‖)
    (defect : ‖contourCentroidGaugeProjection (fixedRelabelEquivalence angular small standardCircleBanach) direction - direction‖ ≤ centroidConstant * ‖direction‖ ^ 2)
    (rawBounds : ‖fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach)‖ ≤ rawConstant ∧
      ‖fderiv ℝ (fderiv ℝ diskEulerRotatingField) (fixedRelabelEquivalence angular small standardCircleBanach)‖ ≤ rawConstant ∧
      ‖diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach + direction) -
        diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach) -
        fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach) direction‖ ≤ rawConstant * ‖direction‖ ^ 2 ∧
      ‖fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach + direction) -
        fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular small standardCircleBanach) -
        fderiv ℝ (fderiv ℝ diskEulerRotatingField) (fixedRelabelEquivalence angular small standardCircleBanach) direction‖ ≤ rawConstant * ‖direction‖ ^ 2) :
    ‖movingStrainAffineResidual (fixedRelabelEquivalence angular small standardCircleBanach) coefficient
      (fixedRelabelEquivalence angular small standardCircleBanach + direction)‖ ≤
      movingStrainAffineBoundConstant rawConstant gaugeConstant correctionConstant centroidConstant * ‖coefficient‖ * ‖direction‖ ^ 2 := by
  have linearDirection := movingStrainAffineLinearResidualCLM_apply_norm_le_defect
    angular small angularMember nearby coefficient direction member
  have remainder := movingStrainAffineResidual_remainder_of_jet_bounds angular small nearby coefficient direction
    rawNonnegative centroidNonnegative directionSmall nextSmall centered defect rawBounds.2
  generalize baseEq : fixedRelabelEquivalence angular small standardCircleBanach = base at *
  let value := movingStrainRealPrimitiveValue base coefficient
  let linear := movingStrainAffineLinearResidualCLM base coefficient
  have valueBound : ‖value‖ ≤ 6 * ‖coefficient‖ := by
    have actual := (movingStrainRealPrimitiveValue_norm_bound base coefficient).trans
      (mul_le_mul_of_nonneg_left baseBound (by positivity : 0 ≤ 2 * ‖coefficient‖))
    convert actual using 1 <;> ring
  have linearBound := movingStrainAffineLinearResidualCLM_norm_bound base coefficient (lt_min_iff.mp nearby).1
  have triangle := norm_add_le (movingStrainAffineResidual base coefficient (base + direction) - linear direction) (linear direction)
  rw [sub_add_cancel] at triangle
  change ‖movingStrainAffineResidual base coefficient (base + direction)‖ ≤
    (centroidConstant + 6 * rawConstant + 3 * rawConstant * correctionConstant +
      (gaugeConstant + 6 * rawConstant + 2 * rawConstant * correctionConstant + correctionConstant) * centroidConstant) *
        ‖coefficient‖ * ‖direction‖ ^ 2
  exact EulerNonuniqueness.General.affine_residual_scale_bound
    rawConstant gaugeConstant correctionConstant centroidConstant ‖coefficient‖ ‖direction‖
    ‖contourCentroidGaugeProjection base‖ ‖fderiv ℝ (fderiv ℝ diskEulerRotatingField) base‖
    ‖value‖ ‖fderiv ℝ diskEulerRotatingField base‖ ‖movingStrainRealCorrectionCLM base coefficient‖
    ‖movingStrainRealCorrectionCLM base (-Complex.I * coefficient)‖ ‖linear‖
    ‖contourCentroidGaugeProjection base direction - direction‖ ‖linear direction‖
    ‖movingStrainAffineResidual base coefficient (base + direction) - linear direction‖
    ‖movingStrainAffineResidual base coefficient (base + direction)‖
    rawNonnegative gaugeNonnegative correctionNonnegative centroidNonnegative (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) gaugeBound rawBounds.2.1 valueBound
    rawBounds.1 correctionBound partnerBound linearBound defect linearDirection remainder triangle

end EulerNonuniqueness.Paper
