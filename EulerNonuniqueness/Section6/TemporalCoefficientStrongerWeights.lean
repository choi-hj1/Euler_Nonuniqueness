import EulerNonuniqueness.Section6.TemporalCoefficientSumBound

noncomputable section

namespace EulerNonuniqueness.Section6

theorem temporalCoefficientEnvelope_radius_inflation {radius distance weight mass factor : ℝ}
    (radiusNonnegative : 0 ≤ radius) (distanceNonnegative : 0 ≤ distance)
    (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass) (factorOne : 1 ≤ factor) (power : ℕ) :
    factor ^ power * temporalCoefficientEnvelope radius distance weight mass power ≤
      temporalCoefficientEnvelope (factor * radius) distance weight mass power := by
  have factorNonnegative : 0 ≤ factor := by linarith
  have radiusBound : radius ≤ factor * radius := by nlinarith
  have bodyBound :
      (((2 * radius / Real.pi) * distance⁻¹ ^ (power + 1) +
        (((power + 3 : ℝ) * 2 ^ (power + 2) + 10) * distance⁻¹ ^ power) / (4 * Real.pi)) * weight ^ 2 +
        (mass / Real.pi * distance⁻¹ ^ (power + 2)) * weight) ≤
      (((2 * (factor * radius) / Real.pi) * distance⁻¹ ^ (power + 1) +
        (((power + 3 : ℝ) * 2 ^ (power + 2) + 10) * distance⁻¹ ^ power) / (4 * Real.pi)) * weight ^ 2 +
        (mass / Real.pi * distance⁻¹ ^ (power + 2)) * weight) := by
    gcongr
  unfold temporalCoefficientEnvelope
  calc
    _ = ((power + 2 : ℕ) : ℝ) * (factor * radius) ^ power / (2 * Real.pi) *
        (((2 * radius / Real.pi) * distance⁻¹ ^ (power + 1) +
          (((power + 3 : ℝ) * 2 ^ (power + 2) + 10) * distance⁻¹ ^ power) / (4 * Real.pi)) * weight ^ 2 +
          (mass / Real.pi * distance⁻¹ ^ (power + 2)) * weight) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left bodyBound (by positivity)

theorem stronger_weight_temporalCoefficientEnvelope_le {radius distance weight mass factor : ℝ}
    (radiusNonnegative : 0 ≤ radius) (distanceNonnegative : 0 ≤ distance)
    (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass) (factorOne : 1 ≤ factor) (power : ℕ) :
    (2 * factor) ^ (power + 1) * temporalCoefficientEnvelope radius distance weight mass power ≤
      factor * ((2 : ℝ) ^ (power + 1) * temporalCoefficientEnvelope (factor * radius) distance weight mass power) := by
  have factorNonnegative : 0 ≤ factor := by linarith
  have estimate := mul_le_mul_of_nonneg_left
    (temporalCoefficientEnvelope_radius_inflation radiusNonnegative distanceNonnegative weightNonnegative
      massNonnegative factorOne power) (show 0 ≤ factor * (2 : ℝ) ^ (power + 1) by positivity)
  convert estimate using 1 <;> simp only [mul_pow, pow_succ] <;> ring

theorem summable_stronger_weight_temporalCoefficientEnvelope {radius distance weight mass factor : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass) (factorOne : 1 ≤ factor)
    (small : 4 * (factor * radius) / distance < 1) :
    Summable (fun power : ℕ => (2 * factor) ^ (power + 1) *
      temporalCoefficientEnvelope radius distance weight mass power) := by
  have factorNonnegative : 0 ≤ factor := by linarith
  apply Summable.of_nonneg_of_le
    (fun power => mul_nonneg (by positivity)
      (temporalCoefficientEnvelope_nonnegative radiusNonnegative positive.le weightNonnegative massNonnegative power))
    (fun power => stronger_weight_temporalCoefficientEnvelope_le radiusNonnegative positive.le
      weightNonnegative massNonnegative factorOne power)
  exact (summable_weighted_temporalCoefficientEnvelope (mul_nonneg factorNonnegative radiusNonnegative)
    positive small weight mass).mul_left factor

theorem tsum_stronger_weight_temporalCoefficientEnvelope_le {radius distance weight mass factor : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass) (factorOne : 1 ≤ factor)
    (small : 8 * (factor * radius) ≤ distance) :
    (∑' power : ℕ, (2 * factor) ^ (power + 1) * temporalCoefficientEnvelope radius distance weight mass power) ≤
      factor * (46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2)) := by
  have factorNonnegative : 0 ≤ factor := by linarith
  have inflatedNonnegative := mul_nonneg factorNonnegative radiusNonnegative
  have strictSmall : 4 * (factor * radius) / distance < 1 :=
    (div_lt_one positive).mpr (by linarith)
  have estimate := Summable.tsum_le_tsum
    (fun power => stronger_weight_temporalCoefficientEnvelope_le radiusNonnegative positive.le
      weightNonnegative massNonnegative factorOne power)
    (summable_stronger_weight_temporalCoefficientEnvelope radiusNonnegative positive weightNonnegative massNonnegative factorOne strictSmall)
    ((summable_weighted_temporalCoefficientEnvelope inflatedNonnegative positive strictSmall weight mass).mul_left factor)
  rw [tsum_mul_left] at estimate
  exact estimate.trans (mul_le_mul_of_nonneg_left
    (tsum_weighted_temporalCoefficientEnvelope_coarse inflatedNonnegative positive weightNonnegative massNonnegative small)
    factorNonnegative)

end EulerNonuniqueness.Section6
