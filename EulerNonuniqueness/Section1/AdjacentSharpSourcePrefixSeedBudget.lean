import EulerNonuniqueness.Section1.AdjacentIncomingPrefixPrefactor

noncomputable section

namespace EulerNonuniqueness.Paper

private theorem adjacent_sharp_normalizations (scales : Scales) (index : ℕ)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {coefficient : ℝ} (coefficientPositive : 0 < coefficient) :
    scales.circulation (index + 1) ^ 2 / (scales.omega index ^ 2 * scales.location index ^ 4) =
        (Real.sqrt 2 * Real.pi ^ 2 / (8 * Real.sqrt 3)) * scales.seed index ∧
    scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
        (scales.omega index * scales.location index ^ 4) =
        (Real.sqrt 2 * Real.pi / (16 * Real.sqrt 3)) * scales.seed index / scales.ratio ∧
    scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
        |scales.location index - scales.location (index + 1)| ^ 4 *
        (1 + scales.location index / scales.location (index + 1)) /
        (coefficient * scales.omega (index + 1)) =
        (3 * Real.sqrt 2 * Real.pi / Real.sqrt 3) * scales.seed index /
          (coefficient * scales.ratio ^ 2) := by
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have locationPositive := scales.location_pos (index + 1)
  have omegaNext : scales.omega (index + 1) = scales.omega index * scales.ratio := by
    simp only [Scales.omega, pow_succ]
    ring
  have locationPrevious : scales.location index = 2 * scales.location (index + 1) := by
    rw [scales.location_eq_inv_pow, scales.location_eq_inv_pow, pow_succ]
    field_simp
  have locationRatio : scales.location index / scales.location (index + 1) = 2 := by
    rw [locationPrevious]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [Scales.seed, scales.adjacent_location_distance, locationRatio,
      Scales.circulation, omegaNext]
    try simp only [locationPrevious, abs_of_pos locationPositive]
    field_simp [coefficientPositive.ne', ratioPositive.ne', omegaPositive.ne', locationPositive.ne',
      Real.pi_ne_zero, (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne',
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']
    ring

theorem Scales.adjacent_sharp_source_prefix_seed_budget_le (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {incoming outgoing extent magnitude distance neutralFactor coefficient weight neutral : ℝ}
    (incomingNonnegative : 0 ≤ incoming) (outgoingNonnegative : 0 ≤ outgoing)
    (extentNonnegative : 0 ≤ extent) (magnitudeNonnegative : 0 ≤ magnitude)
    (distanceNonnegative : 0 ≤ distance) (neutralFactorNonnegative : 0 ≤ neutralFactor)
    (coefficientPositive : 0 < coefficient) (index : ℕ)
    (weightBound : scales.omega index ≤ weight) (neutralNonnegative : 0 ≤ neutral)
    (neutralBound : neutral ≤ neutralFactor * scales.length (index + 1) ^ 2) :
    incoming * extent ^ 2 *
        (scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
          |scales.location index - scales.location (index + 1)| ^ 4 *
          (1 + scales.location index / scales.location (index + 1))) * magnitude /
          (coefficient * scales.omega (index + 1)) +
      outgoing / scales.location index ^ 4 * scales.circulation (index + 1) *
        (scales.circulation (index + 1) / weight ^ 2 +
          ((1 + distance) * scales.length (index + 1) ^ 2 + neutral) / weight) ≤
      (4 * outgoing + 100 * (incoming * extent ^ 2 * magnitude / (coefficient * scales.ratio ^ 2) +
        outgoing * (1 + distance + neutralFactor) / scales.ratio)) * scales.seed index := by
  obtain ⟨quadratic, linear, incomingIdentity⟩ :=
    adjacent_sharp_normalizations scales index frequencyPositive ratioPositive coefficientPositive
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have weightPositive : 0 < weight := omegaPositive.trans_le weightBound
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index + 1)
  have seedNonnegative : 0 ≤ scales.seed index := by
    dsimp only [Scales.seed]
    positivity
  have sqrtTwo : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have sqrtThree : (1 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have quadraticConstant : Real.sqrt 2 * Real.pi ^ 2 / (8 * Real.sqrt 3) ≤ (4 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * Real.sqrt (3 : ℝ))).mpr
    have piSquare : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
    have product := mul_le_mul sqrtTwo piSquare (sq_nonneg Real.pi) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [product, sqrtThree]
  have linearConstant : Real.sqrt 2 * Real.pi / (16 * Real.sqrt 3) ≤ (100 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * Real.sqrt (3 : ℝ))).mpr
    have product := mul_le_mul sqrtTwo Real.pi_lt_four.le Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [product, sqrtThree]
  have incomingConstant : 3 * Real.sqrt 2 * Real.pi / Real.sqrt 3 ≤ (100 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (3 : ℝ))).mpr
    have product := mul_le_mul sqrtTwo Real.pi_lt_four.le Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [product, sqrtThree]
  have incomingEstimate : incoming * extent ^ 2 *
      (scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
        |scales.location index - scales.location (index + 1)| ^ 4 *
        (1 + scales.location index / scales.location (index + 1))) * magnitude /
        (coefficient * scales.omega (index + 1)) ≤
      100 * (incoming * extent ^ 2 * magnitude / (coefficient * scales.ratio ^ 2)) * scales.seed index := by
    have extentSquare := pow_nonneg extentNonnegative 2
    have scaled := mul_le_mul_of_nonneg_right incomingConstant
      (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg incomingNonnegative extentSquare)
        magnitudeNonnegative) seedNonnegative) (by positivity : 0 ≤ coefficient * scales.ratio ^ 2))
    calc
      _ = incoming * extent ^ 2 * magnitude *
          (scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
            |scales.location index - scales.location (index + 1)| ^ 4 *
            (1 + scales.location index / scales.location (index + 1)) /
            (coefficient * scales.omega (index + 1))) := by ring
      _ ≤ _ := by rw [incomingIdentity]; convert scaled using 1 <;> ring
  have numeratorBound : (1 + distance) * scales.length (index + 1) ^ 2 + neutral ≤
      (1 + distance + neutralFactor) * scales.length (index + 1) ^ 2 := by nlinarith only [neutralBound]
  have numeratorNonnegative : 0 ≤ (1 + distance + neutralFactor) * scales.length (index + 1) ^ 2 :=
    (add_nonneg (by positivity : 0 ≤ (1 + distance) * scales.length (index + 1) ^ 2) neutralNonnegative).trans numeratorBound
  have linearWeight := (div_le_div_of_nonneg_right numeratorBound weightPositive.le).trans
    (div_le_div_of_nonneg_left numeratorNonnegative omegaPositive weightBound)
  have quadraticWeight := div_le_div_of_nonneg_left circulationPositive.le (sq_pos_of_pos omegaPositive)
    (pow_le_pow_left₀ omegaPositive.le weightBound 2)
  have outgoingEstimate := mul_le_mul_of_nonneg_left (add_le_add quadraticWeight linearWeight)
    (show 0 ≤ outgoing / scales.location index ^ 4 * scales.circulation (index + 1) by positivity)
  have outgoingNormalization : outgoing / scales.location index ^ 4 * scales.circulation (index + 1) *
      (scales.circulation (index + 1) / scales.omega index ^ 2 +
        ((1 + distance + neutralFactor) * scales.length (index + 1) ^ 2) / scales.omega index) =
      outgoing * ((Real.sqrt 2 * Real.pi ^ 2 / (8 * Real.sqrt 3)) * scales.seed index) +
      outgoing * (1 + distance + neutralFactor) *
        ((Real.sqrt 2 * Real.pi / (16 * Real.sqrt 3)) * scales.seed index / scales.ratio) := by
    rw [← quadratic, ← linear]
    ring
  rw [outgoingNormalization] at outgoingEstimate
  have quadraticScaled := mul_le_mul_of_nonneg_right quadraticConstant (mul_nonneg outgoingNonnegative seedNonnegative)
  have linearScaled := mul_le_mul_of_nonneg_right linearConstant
    (show 0 ≤ outgoing * (1 + distance + neutralFactor) * scales.seed index / scales.ratio by positivity)
  ring_nf at incomingEstimate outgoingEstimate quadraticScaled linearScaled ⊢
  linarith only [incomingEstimate, outgoingEstimate, quadraticScaled, linearScaled]

end EulerNonuniqueness.Paper
