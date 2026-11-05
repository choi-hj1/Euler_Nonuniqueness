import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem small_center_feedback_coefficients
    {frequency length location gap neutral transport tolerance : ℝ}
    (frequencyNonnegative : 0 ≤ frequency) (lengthPositive : 0 < length)
    (locationPositive : 0 < location) (locationSmall : location ≤ 1) (gapPositive : 0 < gap)
    (transportNonnegative : 0 ≤ transport) (neutralFine : neutral ≤ length ^ 2)
    (lengthSmall : length ≤ location) (transportSmall : frequency * length ≤ transport * location)
    (firstBudget : transport ≤ gap ^ 2 * tolerance)
    (secondBudget : 96 * transport ≤ gap ^ 4 * tolerance) :
    frequency * length ^ 2 / (gap ^ 2 * location ^ 2) ≤ tolerance ∧
      (96 * frequency / gap ^ 4) * (neutral / location) ≤ tolerance := by
  constructor
  · apply (div_le_iff₀ (mul_pos (sq_pos_of_pos gapPositive) (sq_pos_of_pos locationPositive))).mpr
    have first := mul_le_mul_of_nonneg_right transportSmall lengthPositive.le
    have second := mul_le_mul_of_nonneg_left lengthSmall
      (show 0 ≤ transport * location by positivity)
    have budget := mul_le_mul_of_nonneg_right firstBudget (sq_nonneg location)
    nlinarith
  · rw [div_mul_div_comm]
    apply (div_le_iff₀ (mul_pos (pow_pos gapPositive _) locationPositive)).mpr
    have neutralBound := mul_le_mul_of_nonneg_left neutralFine
      (show 0 ≤ 96 * frequency by positivity)
    have first := mul_le_mul_of_nonneg_right transportSmall (show 0 ≤ 96 * length by positivity)
    have second := mul_le_mul_of_nonneg_left (lengthSmall.trans locationSmall)
      (show 0 ≤ 96 * transport * location by positivity)
    have budget := mul_le_mul_of_nonneg_right secondBudget locationPositive.le
    nlinarith

end EulerNonuniqueness.General
