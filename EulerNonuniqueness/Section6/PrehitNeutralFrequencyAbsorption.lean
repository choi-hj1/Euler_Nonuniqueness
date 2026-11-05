import EulerNonuniqueness.Section6.NeutralMomentFrequencyAbsorption

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.prehit_neutral_weighted_cost_absorption (scales : Scales) (index : ℕ)
    (frequencyPositive : 0 < scales.frequency) (ratioLarge : 1 ≤ scales.ratio)
    {distance strain hessian initialNeutral : ℝ}
    (distancePositive : 0 < distance) (hessianNonnegative : 0 ≤ hessian)
    (initialBound : initialNeutral ≤ 64 * hessian * scales.length (index + 1) ^ 2)
    (strainSmall : strain ≤ scales.omega index)
    (hessianSmall : hessian * distance ≤ 1 / 16384) :
    (16 * scales.circulation (index + 1) / (Real.pi * distance ^ 3)) *
      (initialNeutral / (2 * Real.sqrt 2 * scales.omega index - strain)) ≤
      (1 / 8 : ℝ) * (Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)) := by
  have ratioPositive : 0 < scales.ratio := lt_of_lt_of_le zero_lt_one ratioLarge
  have receiverPositive := scales.omega_pos frequencyPositive ratioPositive index
  have sourcePositive := scales.omega_pos frequencyPositive ratioPositive (index + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index + 1)
  have sqrtTwoLower : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have sqrtTwoUpper : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have sqrtThreeLower : 3 / 2 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have sourceEquation : scales.omega (index + 1) = scales.omega index * scales.ratio := by
    simp only [Scales.omega, pow_succ, mul_assoc]
  have frequencyComparison : scales.omega index ≤ scales.omega (index + 1) := by
    rw [sourceEquation]
    exact le_mul_of_one_le_right receiverPositive.le ratioLarge
  have ratioBound : scales.omega index / scales.omega (index + 1) ≤ 1 :=
    (div_le_one sourcePositive).mpr frequencyComparison
  have gapLower : scales.omega index ≤ 2 * Real.sqrt 2 * scales.omega index - strain := by
    nlinarith [mul_le_mul_of_nonneg_right sqrtTwoLower receiverPositive.le]
  have fractionBound := div_le_div₀ (by positivity : 0 ≤ 64 * hessian * scales.length (index + 1) ^ 2)
    initialBound receiverPositive gapLower
  have estimate := mul_le_mul_of_nonneg_left fractionBound
    (show 0 ≤ 16 * scales.circulation (index + 1) / (Real.pi * distance ^ 3) by positivity)
  let common := scales.circulation (index + 1) ^ 2 /
    (Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)
  have identity : (16 * scales.circulation (index + 1) / (Real.pi * distance ^ 3)) *
      (64 * hessian * scales.length (index + 1) ^ 2 / scales.omega index) =
      (512 * (hessian * distance)) * (scales.omega index / scales.omega (index + 1)) * common := by
    dsimp only [common]
    rw [Scales.circulation]
    field_simp
    ring
  rw [identity] at estimate
  have ratioRemoved := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ratioBound (show 0 ≤ 512 * (hessian * distance) by positivity))
    (show 0 ≤ common by dsimp only [common]; positivity)
  simp only [mul_one] at ratioRemoved
  have coefficientBound : 512 * (hessian * distance) ≤ Real.sqrt 3 / (16 * Real.sqrt 2) := by
    have scaled := mul_le_mul_of_nonneg_left hessianSmall (by norm_num : (0 : ℝ) ≤ 512)
    apply (le_div_iff₀ (by positivity : 0 < 16 * Real.sqrt 2)).mpr
    nlinarith
  apply estimate.trans (ratioRemoved.trans ?_)
  have multiplied := mul_le_mul_of_nonneg_right coefficientBound
    (show 0 ≤ common by dsimp only [common]; positivity)
  convert multiplied using 1
  dsimp only [common]
  ring

end EulerNonuniqueness.Paper
