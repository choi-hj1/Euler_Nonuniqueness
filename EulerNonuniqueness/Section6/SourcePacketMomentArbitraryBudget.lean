import EulerNonuniqueness.Section6.PaperInitialMomentAbsorption

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.moment_ramp_weighted_arbitrary_cost (scales : Scales) (index : ℕ)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {distance outgoingRadius horizon initialError forcing deformation : ℝ}
    (distancePositive : 0 < distance) (ratioLarge : 1 ≤ scales.ratio)
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance)
    (rateNumeric : 20 * initialError + 83200 / outgoingRadius ^ 2 +
      76 * forcing * horizon + 36 * forcing * outgoingRadius / scales.omega (index + 1) ≤ tolerance / 4)
    (deformationBound : scales.radius (index + 1) ^ 2 * deformation ≤
      tolerance * scales.length (index + 1) ^ 2 / 6144) :
    let rate := 20 * scales.omega (index + 1) * scales.length (index + 1) ^ 2 * initialError +
      83200 * scales.omega (index + 1) * scales.length (index + 1) ^ 2 / outgoingRadius ^ 2 +
      76 * scales.omega (index + 1) * forcing * scales.length (index + 1) ^ 2 * horizon +
      36 * forcing * scales.length (index + 1) ^ 2 * outgoingRadius
    let decay := 2 * Real.sqrt 2 * scales.omega index
    (6 / (Real.pi * distance ^ 4)) *
      (scales.circulation (index + 1) * rate / decay ^ 2 +
        1024 * scales.circulation (index + 1) * scales.radius (index + 1) ^ 2 * deformation / decay) ≤
      tolerance * (Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)) := by
  have receiverPositive := scales.omega_pos frequencyPositive ratioPositive index
  have sourcePositive := scales.omega_pos frequencyPositive ratioPositive (index + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index + 1)
  have lengthPositive := scales.length_pos (index + 1)
  have sqrtTwoPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have sqrtTwoUpper : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have sqrtTwoFourth : Real.sqrt 2 ^ 4 = 4 := by
    calc
      _ = (Real.sqrt 2 ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have sqrtThreeLower : 3 / 2 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have rateBound :
      20 * scales.omega (index + 1) * scales.length (index + 1) ^ 2 * initialError +
        83200 * scales.omega (index + 1) * scales.length (index + 1) ^ 2 / outgoingRadius ^ 2 +
        76 * scales.omega (index + 1) * forcing * scales.length (index + 1) ^ 2 * horizon +
        36 * forcing * scales.length (index + 1) ^ 2 * outgoingRadius ≤
        tolerance * scales.omega (index + 1) * scales.length (index + 1) ^ 2 / 4 := by
    have bound := mul_le_mul_of_nonneg_left rateNumeric
      (show 0 ≤ scales.omega (index + 1) * scales.length (index + 1) ^ 2 by positivity)
    convert bound using 1 <;> field_simp [sourcePositive.ne'] <;> ring
  have sqrtTwoLower : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have denominatorBound : 4 ≤ 4 * Real.sqrt 2 * scales.ratio := by
    have product := mul_le_mul sqrtTwoLower ratioLarge (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg (2 : ℝ))
    nlinarith
  have secondCoefficient : tolerance / (4 * Real.sqrt 2 * scales.ratio) ≤ tolerance / 4 :=
    div_le_div_of_nonneg_left tolerancePositive.le (by norm_num) denominatorBound
  have coefficientLower : 3 / 8 ≤ Real.sqrt 3 / (2 * Real.sqrt 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt 2)).mpr
    nlinarith
  have coefficientBound : 3 * tolerance / 32 + tolerance / (4 * Real.sqrt 2 * scales.ratio) ≤
      tolerance * Real.sqrt 3 / (2 * Real.sqrt 2) := by
    have multiplied := mul_le_mul_of_nonneg_left coefficientLower tolerancePositive.le
    have normalized : 3 * tolerance / 8 ≤ tolerance * Real.sqrt 3 / (2 * Real.sqrt 2) := by
      convert multiplied using 1 <;> ring
    nlinarith
  let common := scales.circulation (index + 1) ^ 2 /
    (Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)
  have commonNonnegative : 0 ≤ common := by dsimp only [common]; positivity
  have omegaNext : scales.omega (index + 1) = scales.ratio * scales.omega index := by
    simp only [Scales.omega, pow_succ]
    ring
  dsimp only
  calc
    _ ≤ (6 / (Real.pi * distance ^ 4)) *
        (scales.circulation (index + 1) * (tolerance * scales.omega (index + 1) * scales.length (index + 1) ^ 2 / 4) /
            (2 * Real.sqrt 2 * scales.omega index) ^ 2 +
          1024 * scales.circulation (index + 1) * (tolerance * scales.length (index + 1) ^ 2 / 6144) /
            (2 * Real.sqrt 2 * scales.omega index)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 6 / (Real.pi * distance ^ 4))
      apply add_le_add
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left rateBound circulationPositive.le) (sq_nonneg _)
      · have multiplied := mul_le_mul_of_nonneg_left deformationBound
          (show 0 ≤ 1024 * scales.circulation (index + 1) by positivity)
        convert div_le_div_of_nonneg_right multiplied
          (show 0 ≤ 2 * Real.sqrt 2 * scales.omega index by positivity) using 1 <;> ring
    _ = (3 * tolerance / 32 + tolerance / (4 * Real.sqrt 2 * scales.ratio)) * common := by
      dsimp only [common]
      simp only [Scales.circulation, omegaNext]
      field_simp [Real.pi_ne_zero, distancePositive.ne', sqrtTwoPositive.ne', receiverPositive.ne', ratioPositive.ne']
      ring_nf
      simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sqrtTwoFourth]
      <;> ring
    _ ≤ (tolerance * Real.sqrt 3 / (2 * Real.sqrt 2)) * common :=
      mul_le_mul_of_nonneg_right coefficientBound commonNonnegative
    _ = _ := by dsimp only [common]; ring

end EulerNonuniqueness.Paper

