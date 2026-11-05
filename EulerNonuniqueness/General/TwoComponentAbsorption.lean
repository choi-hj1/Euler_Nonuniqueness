import Mathlib

namespace EulerNonuniqueness

theorem two_component_absorption {first second firstInput secondInput firstLocal firstReturn secondReturn secondLocal : ℝ}
    (firstDiagonal : 0 ≤ 1 - firstLocal) (secondDiagonal : 0 ≤ 1 - secondLocal)
    (firstReturnNonnegative : 0 ≤ firstReturn) (secondReturnNonnegative : 0 ≤ secondReturn)
    (determinantPositive : 0 < (1 - firstLocal) * (1 - secondLocal) - firstReturn * secondReturn)
    (firstBound : first ≤ firstInput + firstLocal * first + firstReturn * second)
    (secondBound : second ≤ secondInput + secondReturn * first + secondLocal * second) :
    first ≤ ((1 - secondLocal) * firstInput + firstReturn * secondInput) /
      ((1 - firstLocal) * (1 - secondLocal) - firstReturn * secondReturn) ∧
    second ≤ ((1 - firstLocal) * secondInput + secondReturn * firstInput) /
      ((1 - firstLocal) * (1 - secondLocal) - firstReturn * secondReturn) := by
  constructor
  · apply (le_div_iff₀ determinantPositive).mpr
    have firstScaled := mul_le_mul_of_nonneg_left firstBound secondDiagonal
    have secondScaled := mul_le_mul_of_nonneg_left secondBound firstReturnNonnegative
    nlinarith
  · apply (le_div_iff₀ determinantPositive).mpr
    have secondScaled := mul_le_mul_of_nonneg_left secondBound firstDiagonal
    have firstScaled := mul_le_mul_of_nonneg_left firstBound secondReturnNonnegative
    nlinarith

end EulerNonuniqueness
