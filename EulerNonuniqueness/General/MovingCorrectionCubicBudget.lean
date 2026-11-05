import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem forcing_times_square_le_cubic_add_square
    {size epsilon : ℝ} (sizeNonnegative : 0 ≤ size)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonSmall : epsilon ≤ 1) :
    epsilon * size ^ 2 ≤ size ^ 3 + epsilon ^ 2 := by
  by_cases ordered : size ≤ epsilon
  · have squares := sq_le_sq₀ sizeNonnegative epsilonNonnegative |>.mpr ordered
    have weighted := mul_le_mul_of_nonneg_left squares epsilonNonnegative
    have epsilonCube := mul_le_mul_of_nonneg_left epsilonSmall (sq_nonneg epsilon)
    have sizeCube := pow_nonneg sizeNonnegative 3
    nlinarith
  · have weighted := mul_le_mul_of_nonneg_right (le_of_not_ge ordered) (sq_nonneg size)
    nlinarith [sq_nonneg epsilon]

theorem moving_correction_parameter_budget
    {size epsilon constant : ℝ}
    (sizeNonnegative : 0 ≤ size) (sizeSmall : size ≤ 1)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonSmall : epsilon ≤ 1)
    (constantNonnegative : 0 ≤ constant) :
    (epsilon + size ^ 2 + epsilon * size) * (constant * size ^ 2 + epsilon) ≤
      3 * (constant + 1) * (size ^ 3 + epsilon ^ 2) := by
  have young := forcing_times_square_le_cubic_add_square sizeNonnegative epsilonNonnegative epsilonSmall
  have sizeCube := pow_nonneg sizeNonnegative 3
  have fourth : size ^ 4 ≤ size ^ 3 := by
    have weighted := mul_le_mul_of_nonneg_left sizeSmall sizeCube
    nlinarith
  have epsilonCube : epsilon * size ^ 3 ≤ size ^ 3 := by
    simpa only [mul_one, mul_comm] using mul_le_mul_of_nonneg_left epsilonSmall sizeCube
  have epsilonSquare : epsilon ^ 2 * size ≤ epsilon ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left sizeSmall (sq_nonneg epsilon)
  have weightedYoung := mul_le_mul_of_nonneg_left young constantNonnegative
  have weightedFourth := mul_le_mul_of_nonneg_left fourth constantNonnegative
  have weightedCube := mul_le_mul_of_nonneg_left epsilonCube constantNonnegative
  have nonnegativeSquare := mul_nonneg constantNonnegative (sq_nonneg epsilon)
  nlinarith

end EulerNonuniqueness.General
