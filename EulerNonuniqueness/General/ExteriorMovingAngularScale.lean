import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

theorem exteriorMovingAngularScale_le_quadratic_rate
    {frequency constant epsilon radius transverse angular : ℝ}
    (frequencyNonnegative : 0 ≤ frequency) (constantNonnegative : 0 ≤ constant)
    (epsilonNonnegative : 0 ≤ epsilon) (radiusNonnegative : 0 ≤ radius) (radiusSmall : radius ≤ 1)
    (transverseNonnegative : 0 ≤ transverse) (angularNonnegative : 0 ≤ angular)
    (epsilonSmall : epsilon ≤ radius) (squaredSmall : epsilon ^ 2 ≤ radius ^ 3) :
    (constant * epsilon) * (constant * frequency *
        (radius * transverse + radius ^ 2 * angular + epsilon * (transverse + angular))) +
      (constant * epsilon * (transverse + angular)) *
        (constant * frequency * (radius ^ 2 + epsilon * radius)) ≤
      4 * constant ^ 2 * frequency * radius ^ 2 * (transverse + radius * angular) := by
  have cubeLeSquare : radius ^ 3 ≤ radius ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg radius) (sub_nonneg.mpr radiusSmall)]
  have epsilonRadius := mul_le_mul_of_nonneg_right epsilonSmall radiusNonnegative
  have epsilonSquare := mul_le_mul_of_nonneg_right epsilonSmall (sq_nonneg radius)
  have squaredRadius := mul_le_mul_of_nonneg_right squaredSmall radiusNonnegative
  have fourthLeCube : radius ^ 3 * radius ≤ radius ^ 3 :=
    mul_le_of_le_one_right (pow_nonneg radiusNonnegative 3) radiusSmall
  have transverseBound : epsilon * radius + epsilon ^ 2 + epsilon * radius ^ 2 + epsilon ^ 2 * radius ≤ 4 * radius ^ 2 := by
    nlinarith only [epsilonRadius, squaredSmall, cubeLeSquare, epsilonSquare, squaredRadius, fourthLeCube]
  have angularBound : 2 * epsilon * radius ^ 2 + epsilon ^ 2 + epsilon ^ 2 * radius ≤ 4 * radius ^ 3 := by
    nlinarith only [epsilonSquare, squaredSmall, squaredRadius, fourthLeCube]
  have combined := add_le_add (mul_le_mul_of_nonneg_right transverseBound transverseNonnegative)
    (mul_le_mul_of_nonneg_right angularBound angularNonnegative)
  have scaled := mul_le_mul_of_nonneg_left combined
    (mul_nonneg (sq_nonneg constant) frequencyNonnegative)
  convert scaled using 1 <;> ring

end EulerNonuniqueness.General
