import EulerNonuniqueness.Section6.CenteredPointScaling

noncomputable section

namespace EulerNonuniqueness.Section6

theorem normalized_configuration_norm (positions : FourPointConfiguration) {length : ℝ} {rotation : ℂ}
    (lengthPositive : 0 < length) (rotationNorm : ‖rotation‖ = 1) :
    ‖fun target => ((length : ℂ) * rotation)⁻¹ * positions target‖ = ‖positions‖ / length := by
  change ‖((length : ℂ) * rotation)⁻¹ • positions‖ = _
  rw [norm_smul, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos lengthPositive, rotationNorm, mul_one]
  ring

theorem normalized_forcing_norm (forcing : FourPointConfiguration) {frequency length : ℝ} {rotation : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (rotationNorm : ‖rotation‖ = 1) :
    ‖fun target => ((frequency : ℂ) * ((length : ℂ) * rotation))⁻¹ * forcing target‖ =
      ‖forcing‖ / (frequency * length) := by
  change ‖((frequency : ℂ) * ((length : ℂ) * rotation))⁻¹ • forcing‖ = _
  rw [norm_smul, norm_inv, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos lengthPositive, abs_of_pos frequencyPositive,
    rotationNorm, mul_one]
  ring

theorem normalized_forcing_bound_of_centered_bound {forcing positions : FourPointConfiguration}
    {frequency length constant : ℝ} {rotation : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (rotationNorm : ‖rotation‖ = 1)
    (bound : ‖forcing‖ ≤ constant * (‖positions‖ + length)) :
    ‖fun target => ((frequency : ℂ) * ((length : ℂ) * rotation))⁻¹ * forcing target‖ ≤
      (constant / frequency) * (‖fun target => ((length : ℂ) * rotation)⁻¹ * positions target‖ + 1) := by
  rw [normalized_forcing_norm forcing frequencyPositive lengthPositive rotationNorm,
    normalized_configuration_norm positions lengthPositive rotationNorm]
  exact (div_le_div_of_nonneg_right bound (mul_pos frequencyPositive lengthPositive).le).trans_eq (by
    field_simp [frequencyPositive.ne', lengthPositive.ne']
    <;> ring)

end EulerNonuniqueness.Section6
