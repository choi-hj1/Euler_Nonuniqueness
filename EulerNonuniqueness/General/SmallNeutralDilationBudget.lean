import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem small_neutral_dilation_coefficients
    {frequency length location gap memory transport tolerance first second : ℝ}
    (frequencyNonnegative : 0 ≤ frequency) (lengthPositive : 0 < length) (locationPositive : 0 < location)
    (locationSmall : location ≤ 1) (gapPositive : 0 < gap) (memoryNonnegative : 0 ≤ memory)
    (transportNonnegative : 0 ≤ transport) (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second)
    (firstSmall : first ≤ length / 64) (secondSmall : second ≤ length / 64)
    (secondFine : second ≤ memory * length ^ 2)
    (transportSmall : frequency * length ≤ transport * location)
    (firstBudget : transport ≤ 8 * gap ^ 2 * tolerance)
    (secondBudget : 6 * memory * transport ≤ gap ^ 4 * tolerance) :
    (4 * frequency / (gap ^ 2 * location)) * (first + second) ≤ tolerance ∧
      (384 * frequency / gap ^ 4) * (first * second / length ^ 2) ≤ tolerance := by
  constructor
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos gapPositive) locationPositive)).mpr
    have product := mul_le_mul_of_nonneg_left (add_le_add firstSmall secondSmall)
      (show 0 ≤ 4 * frequency by positivity)
    have budget := mul_le_mul_of_nonneg_right firstBudget locationPositive.le
    nlinarith
  · have fraction : (384 * frequency / gap ^ 4) * (first * second / length ^ 2) =
        (384 * frequency * first * second) / (gap ^ 4 * length ^ 2) := by ring
    rw [fraction]
    apply (div_le_iff₀ (mul_pos (pow_pos gapPositive _) (sq_pos_of_pos lengthPositive))).mpr
    have product := mul_le_mul firstSmall secondFine secondNonnegative
      (show 0 ≤ length / 64 by positivity)
    have scaled := mul_le_mul_of_nonneg_left product (show 0 ≤ 384 * frequency by positivity)
    have speed : frequency * length ≤ transport :=
      transportSmall.trans (mul_le_of_le_one_right transportNonnegative locationSmall)
    have multiplied := mul_le_mul_of_nonneg_right speed (show 0 ≤ 6 * memory * length ^ 2 by positivity)
    have budget := mul_le_mul_of_nonneg_right secondBudget (sq_nonneg length)
    nlinarith

end EulerNonuniqueness.General
