import EulerNonuniqueness.Section6.TemporalCoefficientSummability

noncomputable section

namespace EulerNonuniqueness.Section6

def temporalCoefficientEnvelope (radius distance weight mass : ℝ) (power : ℕ) : ℝ :=
  ((power + 2 : ℕ) : ℝ) * radius ^ power / (2 * Real.pi) *
    (((2 * radius / Real.pi) * distance⁻¹ ^ (power + 1) +
      (((power + 3 : ℝ) * 2 ^ (power + 2) + 10) * distance⁻¹ ^ power) / (4 * Real.pi)) * weight ^ 2 +
      (mass / Real.pi * distance⁻¹ ^ (power + 2)) * weight)

theorem temporalCoefficientEnvelope_nonnegative {radius distance weight mass : ℝ}
    (radiusNonnegative : 0 ≤ radius) (distanceNonnegative : 0 ≤ distance)
    (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass) (power : ℕ) :
    0 ≤ temporalCoefficientEnvelope radius distance weight mass power := by
  unfold temporalCoefficientEnvelope
  positivity

theorem temporalCoefficientEnvelope_mono {radius distance firstWeight secondWeight firstMass secondMass : ℝ}
    (radiusNonnegative : 0 ≤ radius) (distanceNonnegative : 0 ≤ distance)
    (weightNonnegative : 0 ≤ firstWeight) (massNonnegative : 0 ≤ firstMass)
    (weightBound : firstWeight ≤ secondWeight) (massBound : firstMass ≤ secondMass) (power : ℕ) :
    temporalCoefficientEnvelope radius distance firstWeight firstMass power ≤
      temporalCoefficientEnvelope radius distance secondWeight secondMass power := by
  have secondMassNonnegative : 0 ≤ secondMass := massNonnegative.trans massBound
  unfold temporalCoefficientEnvelope
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ weightNonnegative weightBound 2) (by positivity)
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right massBound Real.pi_pos.le) (by positivity)
    · exact weightBound
    · exact weightNonnegative
    · positivity

theorem summable_weighted_temporalCoefficientEnvelope {radius distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (small : 4 * radius / distance < 1) (weight mass : ℝ) :
    Summable (fun power : ℕ => (2 : ℝ) ^ (power + 1) *
      temporalCoefficientEnvelope radius distance weight mass power) :=
  summable_temporalCoefficientEnvelope radiusNonnegative positive small weight mass

end EulerNonuniqueness.Section6
