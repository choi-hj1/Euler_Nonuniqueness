import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem contour_four_scale_rate_bound
    {frequency weight ratio amplitude radius transverse relative cost constant : ℝ}
    (constantOne : 1 ≤ constant) (frequencyNonnegative : 0 ≤ frequency)
    (weightNonnegative : 0 ≤ weight) (ratioNonnegative : 0 ≤ ratio)
    (amplitudeNonnegative : 0 ≤ amplitude) (radiusNonnegative : 0 ≤ radius)
    (transverseNonnegative : 0 ≤ transverse) (relativeNonnegative : 0 ≤ relative)
    (transverseBound : transverse ≤ constant * radius)
    (relativeBound : relative ≤ constant * radius)
    (costBound : cost ≤ constant * (weight * radius ^ 2 + amplitude)) :
    frequency * transverse ^ 3 + weight * relative ^ 2 + weight * ratio * relative + amplitude + cost ≤
      (constant ^ 3 + constant ^ 2 + 2 * constant + 1) *
        (frequency * radius ^ 3 + weight * radius ^ 2 + weight * ratio * radius + amplitude) := by
  have constantNonnegative : 0 ≤ constant := by linarith
  have cubic := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ transverseNonnegative transverseBound 3) frequencyNonnegative
  have quadratic := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ relativeNonnegative relativeBound 2) weightNonnegative
  have linear := mul_le_mul_of_nonneg_left relativeBound (mul_nonneg weightNonnegative ratioNonnegative)
  have direct := add_le_add (add_le_add (add_le_add cubic quadratic) linear) (le_rfl : amplitude ≤ amplitude)
  have total := add_le_add direct costBound
  have c3 : 0 ≤ constant ^ 3 := by positivity
  have c2 : 0 ≤ constant ^ 2 := sq_nonneg constant
  have first : 0 ≤ frequency * radius ^ 3 := by positivity
  have second : 0 ≤ weight * radius ^ 2 := by positivity
  have third : 0 ≤ weight * ratio * radius := by positivity
  have firstExtra := mul_nonneg (by positivity : 0 ≤ constant ^ 2 + 2 * constant + 1) first
  have secondExtra := mul_nonneg (by positivity : 0 ≤ constant ^ 3 + constant + 1) second
  have thirdExtra := mul_nonneg (by positivity : 0 ≤ constant ^ 3 + constant ^ 2 + constant + 1) third
  have amplitudeExtra := mul_nonneg (by positivity : 0 ≤ constant ^ 3 + constant ^ 2 + constant) amplitudeNonnegative
  nlinarith [total]

end EulerNonuniqueness.General
