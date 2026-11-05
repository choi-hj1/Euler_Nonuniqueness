import EulerNonuniqueness.General.CubicFiberCoefficient

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace

theorem quadratic_velocity_bilinear_relative_cubic
    (first second : BilinearEnd Space) (firstVelocity secondVelocity initial final : Space)
    {coefficientBound velocityBound distance : ℝ}
    (coefficientNonnegative : 0 ≤ coefficientBound) (velocityNonnegative : 0 ≤ velocityBound)
    (distanceNonnegative : 0 ≤ distance)
    (coefficientNorm : ‖first‖ ≤ coefficientBound)
    (coefficientDifference : ‖first - second‖ ≤ coefficientBound * distance)
    (velocityDifference : ‖firstVelocity - secondVelocity‖ ≤ velocityBound *
      ((‖initial‖ + ‖final‖) * ‖initial - final‖ + (‖initial‖ + ‖final‖) ^ 2 * distance))
    (secondVelocityNorm : ‖secondVelocity‖ ≤ velocityBound * ‖final‖ ^ 2) :
    ‖first firstVelocity initial - second secondVelocity final‖ ≤
      (2 * coefficientBound * velocityBound) *
        ((‖initial‖ + ‖final‖) ^ 2 * ‖initial - final‖ + (‖initial‖ + ‖final‖) ^ 3 * distance) := by
  have bilinearBound (operator : BilinearEnd Space) (left right : Space) :
      ‖operator left right‖ ≤ ‖operator‖ * ‖left‖ * ‖right‖ :=
    (operator left).le_opNorm right |>.trans
      (mul_le_mul_of_nonneg_right (operator.le_opNorm left) (norm_nonneg right))
  have identity : first firstVelocity initial - second secondVelocity final =
      first (firstVelocity - secondVelocity) initial + first secondVelocity (initial - final) +
        (first - second) secondVelocity final := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  let size := ‖initial‖ + ‖final‖
  have initialBound : ‖initial‖ ≤ size := le_add_of_nonneg_right (norm_nonneg _)
  have finalBound : ‖final‖ ≤ size := le_add_of_nonneg_left (norm_nonneg _)
  have finalSquare : ‖final‖ ^ 2 ≤ size ^ 2 := pow_le_pow_left₀ (norm_nonneg _) finalBound _
  have enlargedVelocity : ‖secondVelocity‖ ≤ velocityBound * size ^ 2 :=
    secondVelocityNorm.trans (mul_le_mul_of_nonneg_left finalSquare velocityNonnegative)
  rw [identity]
  calc
    _ ≤ (‖first‖ * ‖firstVelocity - secondVelocity‖ * ‖initial‖ +
        ‖first‖ * ‖secondVelocity‖ * ‖initial - final‖) +
        ‖first - second‖ * ‖secondVelocity‖ * ‖final‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (bilinearBound _ _ _) (bilinearBound _ _ _)))
        (bilinearBound _ _ _))
    _ ≤ (coefficientBound * (velocityBound * (size * ‖initial - final‖ + size ^ 2 * distance)) * size +
        coefficientBound * (velocityBound * size ^ 2) * ‖initial - final‖) +
        (coefficientBound * distance) * (velocityBound * size ^ 2) * size := by gcongr
    _ = _ := by ring

end

end EulerNonuniqueness.General
