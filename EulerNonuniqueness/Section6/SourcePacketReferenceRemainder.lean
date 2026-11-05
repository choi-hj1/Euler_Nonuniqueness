import EulerNonuniqueness.Section6.InitialMomentFrequencyAbsorption

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.reference_multipole_remainder_weighted_seed_absorption
    (scales : Scales) (index : ℕ) (frequencyPositive : 0 < scales.frequency)
    (ratioLarge : 1 ≤ scales.ratio) {distance : ℝ} (distancePositive : 0 < distance)
    (sourceSmall : scales.length (index + 1) / distance ≤ 1 / 1048576) :
    (1408 * scales.circulation (index + 1) * (4 * scales.length (index + 1)) ^ 3 /
      (Real.pi * distance ^ 5)) / (2 * Real.sqrt 2 * scales.omega index) ≤
        (1 / 8 : ℝ) * (Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
          (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)) := by
  have ratioPositive : 0 < scales.ratio := zero_lt_one.trans_le ratioLarge
  have receiverPositive := scales.omega_pos frequencyPositive ratioPositive index
  have sqrtTwoPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have sqrtThreePositive : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have sqrtThreeLower : 3 / 2 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have denominatorLower : (3 / 2 : ℝ) ≤ Real.sqrt 3 * scales.ratio := by
    simpa only [mul_one] using mul_le_mul sqrtThreeLower ratioLarge (by norm_num : (0 : ℝ) ≤ 1)
      sqrtThreePositive.le
  have factorBound : 45056 * (scales.length (index + 1) / distance) /
      (Real.sqrt 3 * scales.ratio) ≤ (1 / 8 : ℝ) := by
    apply (div_le_iff₀ (mul_pos sqrtThreePositive ratioPositive)).mpr
    nlinarith
  have omegaNext : scales.omega (index + 1) = scales.ratio * scales.omega index := by
    simp only [Scales.omega, pow_succ]
    ring
  have identity :
      (1408 * scales.circulation (index + 1) * (4 * scales.length (index + 1)) ^ 3 /
        (Real.pi * distance ^ 5)) / (2 * Real.sqrt 2 * scales.omega index) =
      (45056 * (scales.length (index + 1) / distance) / (Real.sqrt 3 * scales.ratio)) *
        (Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
          (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)) := by
    simp only [Scales.circulation, omegaNext]
    field_simp [Real.pi_ne_zero, distancePositive.ne', sqrtTwoPositive.ne', sqrtThreePositive.ne',
      receiverPositive.ne', ratioPositive.ne']
    <;> ring
  rw [identity]
  exact mul_le_mul_of_nonneg_right factorBound (by positivity)

end EulerNonuniqueness.Paper
