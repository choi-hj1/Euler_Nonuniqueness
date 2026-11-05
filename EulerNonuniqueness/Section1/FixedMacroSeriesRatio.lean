import EulerNonuniqueness.Section1.DyadicSeparation

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.fixed_macro_series_ratio_le_half (scales : Scales) {factor : ℝ}
    (factorNonnegative : 0 ≤ factor) (factorSmall : factor ≤ 1)
    {receiver source : ℕ} (different : receiver ≠ source) :
    8 * 96 * (factor / 39321600 * scales.location receiver) /
        (|scales.location receiver - scales.location source| / 8) ≤ 1 / 2 := by
  have distancePositive := div_pos (scales.location_distance_pos different) (by norm_num : (0 : ℝ) < 8)
  have locations := scales.location_sum_le_three_distance different
  have sourcePositive := scales.location_pos source
  have receiverPositive := scales.location_pos receiver
  have factorBound := mul_le_mul_of_nonneg_right factorSmall receiverPositive.le
  apply (div_le_iff₀ distancePositive).mpr
  nlinarith

end EulerNonuniqueness.Paper
