import EulerNonuniqueness.Section6.PhysicalVorticityStrainMultipole

noncomputable section

namespace EulerNonuniqueness.Section6

theorem physicalMomentRamp_strain_identity (frequency length elapsed : ℝ) (direction displacement : ℂ) :
    -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (
      3 * (-4 * Complex.I * ((2 * Real.pi * frequency * length ^ 2 : ℝ) : ℂ) *
        (frequency : ℂ) * (length : ℂ) ^ 2 * direction ^ 2 * (elapsed : ℂ)) / displacement ^ 4) =
      12 * (frequency : ℂ) ^ 2 * (length : ℂ) ^ 4 * star direction ^ 2 * (elapsed : ℂ) /
        star displacement ^ 4 := by
  push_cast
  simp only [Complex.star_def, map_mul, map_div₀, map_pow, map_neg, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  ring_nf
  simp only [Complex.I_sq]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  <;> ring

theorem physicalMomentRamp_strain_coefficient_positive {frequency length : ℝ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) :
    0 < 12 * frequency ^ 2 * length ^ 4 := by positivity

end EulerNonuniqueness.Section6
