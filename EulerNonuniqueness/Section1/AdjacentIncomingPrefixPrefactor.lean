import EulerNonuniqueness.Section1.Scales
import EulerNonuniqueness.Section5.CascadeStatement

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.adjacent_incoming_prefix_prefactor_le (scales : Scales) (index : ℕ)
    {coefficient : ℝ} (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (coefficientPositive : 0 < coefficient)
    (rateSeparated : 2 * Real.sqrt 2 * scales.omega index ≤ coefficient * scales.omega (index + 1) / 2) :
    0 < coefficient * scales.omega (index + 1) - 2 * Real.sqrt 2 * scales.omega index ∧
    (scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
        |scales.location index - scales.location (index + 1)| ^ 4 *
        (1 + scales.location index / scales.location (index + 1))) /
      (coefficient * scales.omega (index + 1) - 2 * Real.sqrt 2 * scales.omega index) ≤
        (100 / coefficient) * scales.seed index / scales.ratio ^ 2 := by
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have nextPositive := scales.omega_pos frequencyPositive ratioPositive (index + 1)
  have locationPositive := scales.location_pos (index + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index + 1)
  have lengthPositive := scales.length_pos (index + 1)
  have omegaNext : scales.omega (index + 1) = scales.omega index * scales.ratio := by
    simp only [Scales.omega, pow_succ]
    ring
  have locationRatio : scales.location index / scales.location (index + 1) = 2 := by
    rw [scales.location_eq_inv_pow, scales.location_eq_inv_pow, pow_succ]
    field_simp
  have halfPositive : 0 < coefficient * scales.omega (index + 1) / 2 := by positivity
  have gapLower : coefficient * scales.omega (index + 1) / 2 ≤
      coefficient * scales.omega (index + 1) - 2 * Real.sqrt 2 * scales.omega index := by
    linarith only [rateSeparated]
  have gapPositive := halfPositive.trans_le gapLower
  refine ⟨gapPositive, ?_⟩
  rw [locationRatio, scales.adjacent_location_distance]
  norm_num only [show (1 : ℝ) + 2 = 3 by norm_num]
  have numeratorNonnegative : 0 ≤ scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
      scales.location (index + 1) ^ 4 * 3 := by positivity
  have denominatorComparison := div_le_div_of_nonneg_left numeratorNonnegative halfPositive gapLower
  have exactNormalization :
      (scales.circulation (index + 1) * scales.length (index + 1) ^ 2 / scales.location (index + 1) ^ 4 * 3) /
        (coefficient * scales.omega (index + 1) / 2) =
      ((6 * Real.pi * Real.sqrt 2 / Real.sqrt 3) / coefficient) * scales.seed index / scales.ratio ^ 2 := by
    simp only [Scales.seed, scales.adjacent_location_distance, Scales.circulation, omegaNext]
    field_simp [coefficientPositive.ne', ratioPositive.ne', omegaPositive.ne', locationPositive.ne',
      Real.pi_ne_zero, (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne',
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']
    ; ring
  have sqrtTwoBound : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have sqrtThreeOne : (1 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have numericBound : 6 * Real.pi * Real.sqrt 2 / Real.sqrt 3 ≤ (100 : ℝ) := by
    have productBound : 6 * Real.pi * Real.sqrt 2 ≤ 48 := by
      calc
        _ ≤ 6 * 4 * 2 := mul_le_mul (mul_le_mul_of_nonneg_left Real.pi_lt_four.le (by norm_num))
          sqrtTwoBound (Real.sqrt_nonneg _) (by norm_num)
        _ = _ := by norm_num
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mpr
    linarith only [productBound, sqrtThreeOne]
  have seedNonnegative : 0 ≤ scales.seed index := by
    dsimp only [Scales.seed]
    positivity
  have coefficientComparison := div_le_div_of_nonneg_right numericBound coefficientPositive.le
  have scaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right coefficientComparison seedNonnegative) (sq_nonneg scales.ratio)
  exact denominatorComparison.trans (exactNormalization.trans_le scaled)

end EulerNonuniqueness.Paper
