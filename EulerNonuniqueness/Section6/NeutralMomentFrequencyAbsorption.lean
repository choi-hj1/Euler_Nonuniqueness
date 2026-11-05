import EulerNonuniqueness.Section6.PhysicalFieldScaleBounds

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.neutral_moment_weighted_cost_absorption (scales : Scales) (index : ℕ)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {distance sourceRadius strain hessian deformation : ℝ}
    (distancePositive : 0 < distance) (hessianNonnegative : 0 ≤ hessian)
    (sourceFrequencyLarge : 1 ≤ scales.omega (index + 1))
    (strainSmall : strain ≤ scales.omega index)
    (hessianSmall : hessian * distance ≤ 1 / 16384)
    (sourceRadiusBound : sourceRadius ≤ 4 * scales.omega (index + 1) * scales.length (index + 1))
    (patchRadiusBound : scales.radius (index + 1) ≤ scales.length (index + 1))
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16) :
    (16 * scales.circulation (index + 1) / (Real.pi * distance ^ 3)) *
      (hessian * (sourceRadius * scales.length (index + 1) +
        1024 * scales.radius (index + 1) ^ 2 * deformation) /
        (2 * Real.sqrt 2 * scales.omega index - strain) ^ 2) ≤
      (1 / 8 : ℝ) * (Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)) := by
  have receiverPositive := scales.omega_pos frequencyPositive ratioPositive index
  have sourcePositive := scales.omega_pos frequencyPositive ratioPositive (index + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index + 1)
  have lengthPositive := scales.length_pos (index + 1)
  have sqrtTwoLower : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have sqrtTwoUpper : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have sqrtThreeLower : 3 / 2 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have gapLower : scales.omega index ≤ 2 * Real.sqrt 2 * scales.omega index - strain := by
    nlinarith [mul_le_mul_of_nonneg_right sqrtTwoLower receiverPositive.le]
  have deformationBound : scales.radius (index + 1) ^ 2 * deformation ≤ scales.length (index + 1) ^ 2 / 16 := by
    calc
      _ ≤ scales.length (index + 1) ^ 2 * (1 / 16) := by
        exact mul_le_mul (pow_le_pow_left₀ (Real.sqrt_nonneg _) patchRadiusBound 2)
          deformationSmall deformationNonnegative (sq_nonneg _)
      _ = _ := by ring
  have sourceLengthBound := mul_le_mul_of_nonneg_left sourceFrequencyLarge (sq_nonneg (scales.length (index + 1)))
  have radiusLengthBound := mul_le_mul_of_nonneg_right sourceRadiusBound lengthPositive.le
  have rateBound : hessian * (sourceRadius * scales.length (index + 1) +
      1024 * scales.radius (index + 1) ^ 2 * deformation) ≤
      68 * hessian * scales.omega (index + 1) * scales.length (index + 1) ^ 2 := by
    have interiorBound : sourceRadius * scales.length (index + 1) +
        1024 * scales.radius (index + 1) ^ 2 * deformation ≤
        68 * scales.omega (index + 1) * scales.length (index + 1) ^ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left interiorBound hessianNonnegative).trans_eq (by ring)
  have denominatorBound := pow_le_pow_left₀ receiverPositive.le gapLower 2
  have fractionBound := div_le_div₀ (by positivity : 0 ≤ 68 * hessian * scales.omega (index + 1) * scales.length (index + 1) ^ 2)
    rateBound (sq_pos_of_pos receiverPositive) denominatorBound
  have estimate := mul_le_mul_of_nonneg_left fractionBound
    (show 0 ≤ 16 * scales.circulation (index + 1) / (Real.pi * distance ^ 3) by positivity)
  let common := scales.circulation (index + 1) ^ 2 /
    (Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)
  have identity : (16 * scales.circulation (index + 1) / (Real.pi * distance ^ 3)) *
      (68 * hessian * scales.omega (index + 1) * scales.length (index + 1) ^ 2 / scales.omega index ^ 2) =
      (544 * (hessian * distance)) * common := by
    dsimp only [common]
    rw [Scales.circulation]
    field_simp
    <;> ring
  rw [identity] at estimate
  have coefficientLower : 3 / 64 ≤ Real.sqrt 3 / (16 * Real.sqrt 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 16 * Real.sqrt 2)).mpr
    nlinarith
  have coefficientBound : 544 * (hessian * distance) ≤ Real.sqrt 3 / (16 * Real.sqrt 2) := by
    have scaled := mul_le_mul_of_nonneg_left hessianSmall (by norm_num : (0 : ℝ) ≤ 544)
    linarith
  apply estimate.trans
  have multiplied := mul_le_mul_of_nonneg_right coefficientBound (show 0 ≤ common by dsimp only [common]; positivity)
  convert multiplied using 1
  dsimp only [common]
  ring

end EulerNonuniqueness.Paper
