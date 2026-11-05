import EulerNonuniqueness.Section6.InitialMomentWeightedForcing
import EulerNonuniqueness.Section6.PaperPairedMomentSize

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem Scales.initial_moment_weighted_cost_absorption (scales : Scales) (index : ℕ)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {distance outgoingRadius deformation : ℝ} (distancePositive : 0 < distance)
    (outgoingRadiusLarge : 32 ≤ outgoingRadius) (ratioLarge : 96 * outgoingRadius ≤ scales.ratio)
    (radiusSmall : scales.radius (index + 1) ≤ scales.length (index + 1))
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16)
    (moment : ℂ)
    (momentBound : ‖moment‖ ≤
      5 * scales.circulation (index + 1) * scales.length (index + 1) ^ 2 * outgoingRadius +
      512 * scales.circulation (index + 1) * scales.radius (index + 1) ^ 2 * deformation) :
    6 * ‖moment‖ / (Real.pi * distance ^ 4 * (2 * Real.sqrt 2 * scales.omega index)) ≤
      (1 / 8 : ℝ) * (Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)) := by
  have receiverPositive := scales.omega_pos frequencyPositive ratioPositive index
  have sourcePositive := scales.omega_pos frequencyPositive ratioPositive (index + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index + 1)
  have lengthPositive := scales.length_pos (index + 1)
  have sqrtTwoPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have sqrtThreePositive : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have sqrtThreeLower : 3 / 2 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have radiusSquare : scales.radius (index + 1) ^ 2 ≤ scales.length (index + 1) ^ 2 :=
    sq_le_sq₀ (Real.sqrt_nonneg _) lengthPositive.le |>.mpr radiusSmall
  have momentCoarse : ‖moment‖ ≤
      6 * scales.circulation (index + 1) * scales.length (index + 1) ^ 2 * outgoingRadius := by
    have deformationBound : 512 * scales.circulation (index + 1) * scales.radius (index + 1) ^ 2 * deformation ≤
        32 * scales.circulation (index + 1) * scales.length (index + 1) ^ 2 := by
      calc
        _ ≤ 512 * scales.circulation (index + 1) * scales.length (index + 1) ^ 2 * (1 / 16) := by gcongr
        _ = _ := by ring
    nlinarith [mul_le_mul_of_nonneg_left outgoingRadiusLarge
      (show 0 ≤ scales.circulation (index + 1) * scales.length (index + 1) ^ 2 by positivity)]
  have seedNonnegative : 0 ≤ Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
      (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4) := by positivity
  have factorBound : 18 * outgoingRadius / (Real.sqrt 3 * scales.ratio) ≤ (1 / 8 : ℝ) := by
    apply (div_le_iff₀ (mul_pos sqrtThreePositive ratioPositive)).mpr
    nlinarith [mul_le_mul_of_nonneg_right sqrtThreeLower ratioPositive.le]
  have omegaNext : scales.omega (index + 1) = scales.ratio * scales.omega index := by
    simp only [Scales.omega, pow_succ]
    ring
  calc
    _ ≤ 6 * (6 * scales.circulation (index + 1) * scales.length (index + 1) ^ 2 * outgoingRadius) /
        (Real.pi * distance ^ 4 * (2 * Real.sqrt 2 * scales.omega index)) := by gcongr
    _ = (18 * outgoingRadius / (Real.sqrt 3 * scales.ratio)) *
        (Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
          (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)) := by
      simp only [Scales.circulation, omegaNext]
      field_simp [Real.pi_ne_zero, distancePositive.ne', sqrtTwoPositive.ne', sqrtThreePositive.ne',
        receiverPositive.ne', ratioPositive.ne']
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right factorBound seedNonnegative

end EulerNonuniqueness.Paper
