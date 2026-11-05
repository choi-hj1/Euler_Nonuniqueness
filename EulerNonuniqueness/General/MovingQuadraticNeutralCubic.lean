import EulerNonuniqueness.General.MovingQuadraticParameterDifference

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Parameter : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace movingParameterOperatorGroup

theorem moving_quadratic_neutral_correction_relative_cubic
    (first second : Parameter →L[ℝ] BilinearEnd Space)
    (firstVelocity secondVelocity : Parameter) (initial final : Space)
    {coefficientBound velocityBound distance : ℝ}
    (coefficientNonnegative : 0 ≤ coefficientBound) (velocityNonnegative : 0 ≤ velocityBound)
    (distanceNonnegative : 0 ≤ distance) (small : ‖initial‖ + ‖final‖ ≤ 1)
    (coefficientNorm : ‖first‖ ≤ coefficientBound)
    (coefficientDifference : ‖first - second‖ ≤ coefficientBound * distance)
    (velocityDifference : ‖firstVelocity - secondVelocity‖ ≤ velocityBound *
      ((‖initial‖ + ‖final‖) * ‖initial - final‖ + (‖initial‖ + ‖final‖) ^ 2 * distance))
    (secondVelocityNorm : ‖secondVelocity‖ ≤ velocityBound * ‖final‖ ^ 2) :
    ‖first firstVelocity initial initial - second secondVelocity final final‖ ≤
      (2 * coefficientBound * velocityBound) *
        ((‖initial‖ + ‖final‖) ^ 2 * ‖initial - final‖ + (‖initial‖ + ‖final‖) ^ 3 * distance) := by
  let size := ‖initial‖ + ‖final‖
  have sizeNonnegative : 0 ≤ size := by dsimp only [size]; positivity
  have sizeSmall : size ≤ 1 := small
  have firstSquare : ‖initial‖ ^ 2 ≤ size ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg _)) _
  have secondSquare : ‖final‖ ^ 2 ≤ size ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left (norm_nonneg _)) _
  have cubeSmall : size ^ 3 ≤ size ^ 2 := by
    have := mul_le_mul_of_nonneg_left sizeSmall (sq_nonneg size)
    nlinarith only [this]
  have quarticSmall : size ^ 4 ≤ size ^ 3 := by
    have := mul_le_mul_of_nonneg_left sizeSmall (pow_nonneg sizeNonnegative 3)
    nlinarith only [this]
  have enlargedVelocity : ‖secondVelocity‖ ≤ velocityBound * size ^ 2 :=
    secondVelocityNorm.trans (mul_le_mul_of_nonneg_left secondSquare velocityNonnegative)
  calc
    _ ≤ ‖first‖ * ‖firstVelocity - secondVelocity‖ * ‖initial‖ ^ 2 +
        ‖first‖ * ‖secondVelocity‖ * size * ‖initial - final‖ +
        ‖first - second‖ * ‖secondVelocity‖ * ‖final‖ ^ 2 :=
      moving_quadratic_parameter_difference_norm_le _ _ _ _ _ _
    _ ≤ coefficientBound * (velocityBound * (size * ‖initial - final‖ + size ^ 2 * distance)) * size ^ 2 +
        coefficientBound * (velocityBound * size ^ 2) * size * ‖initial - final‖ +
        (coefficientBound * distance) * (velocityBound * size ^ 2) * size ^ 2 := by
      gcongr
    _ = (2 * coefficientBound * velocityBound) * (size ^ 3 * ‖initial - final‖ + size ^ 4 * distance) := by ring
    _ ≤ _ := by gcongr

end

end EulerNonuniqueness.General
