import EulerNonuniqueness.Section6.PairedDipoleStrain

noncomputable section

namespace EulerNonuniqueness.Section6

def fourPointExternalPointVelocity (coefficient : ℝ) (positions : FourPointConfiguration) (location : ℂ) : ℂ :=
  Complex.I * (coefficient : ℂ) * star (fourPointCauchyField positions location)

def fourPointExternalPointStrain (coefficient : ℝ) (positions : FourPointConfiguration) (location : ℂ) : ℂ :=
  Complex.I * (coefficient : ℂ) * star (fourPointCauchyStrain positions location)

theorem fourPointCauchyField_conjugate (positions : FourPointConfiguration) (location : ℂ) :
    star (fourPointCauchyField positions location) =
      fourPointCauchyField (fun target => star (positions target)) (star location) := by
  simp [fourPointCauchyField, star_sum, star_div₀, star_sub]

theorem fourPointCauchyStrain_conjugate (positions : FourPointConfiguration) (location : ℂ) :
    star (fourPointCauchyStrain positions location) =
      fourPointCauchyStrain (fun target => star (positions target)) (star location) := by
  simp [fourPointCauchyStrain, star_sum, star_div₀, star_sub]

theorem fourPointExternalPointVelocity_literal (coefficient : ℝ) (positions : FourPointConfiguration) (location : ℂ) :
    fourPointExternalPointVelocity coefficient positions location =
      Complex.I * ∑ target : Fin 4, (coefficient * fourPointSign target : ℝ) / star (location - positions target) := by
  rw [fourPointExternalPointVelocity, fourPointCauchyField_conjugate]
  simp only [fourPointCauchyField, Complex.ofReal_mul]
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro target _
  simp only [star_sub]
  ring

theorem fourPointExternalPointStrain_hasDerivAt (coefficient : ℝ) (positions : FourPointConfiguration)
    {location : ℂ} (noncollision : ∀ target, location - positions target ≠ 0) :
    HasDerivAt (fun conjugateLocation => Complex.I * (coefficient : ℂ) *
      fourPointCauchyField (fun target => star (positions target)) conjugateLocation)
      (fourPointExternalPointStrain coefficient positions location) (star location) := by
  have derivative := fourPointCauchyField_hasDerivAt (fun target => star (positions target))
    (location := star location)
    (fun target => by simpa only [star_sub] using star_ne_zero.mpr (noncollision target))
  simpa only [fourPointExternalPointStrain, fourPointCauchyStrain_conjugate] using
    derivative.const_mul (Complex.I * (coefficient : ℂ))

theorem twoDipole_physical_strain_far_field (coefficient : ℝ)
    {firstCenter secondCenter firstSeparation secondSeparation location : ℂ} {length : ℝ}
    (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (separated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (far : ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2) :
    ‖fourPointExternalPointStrain coefficient
        (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location +
      2 * Complex.I * (coefficient : ℂ) * star (firstSeparation + secondSeparation) /
        star (location - (firstCenter + secondCenter) / 2) ^ 3 +
      3 * Complex.I * (coefficient : ℂ) * star ((firstCenter - secondCenter) * (firstSeparation - secondSeparation)) /
        star (location - (firstCenter + secondCenter) / 2) ^ 4‖ ≤
      704 * |coefficient| * ‖firstCenter - secondCenter‖ ^ 2 * length /
        ‖location - (firstCenter + secondCenter) / 2‖ ^ 5 := by
  have estimate := twoDipole_CauchyStrain_far_field lengthPositive firstBound secondBound separated far
  have identity : fourPointExternalPointStrain coefficient
        (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location +
      2 * Complex.I * (coefficient : ℂ) * star (firstSeparation + secondSeparation) /
        star (location - (firstCenter + secondCenter) / 2) ^ 3 +
      3 * Complex.I * (coefficient : ℂ) * star ((firstCenter - secondCenter) * (firstSeparation - secondSeparation)) /
        star (location - (firstCenter + secondCenter) / 2) ^ 4 =
      (Complex.I * (coefficient : ℂ)) * star
        (fourPointCauchyStrain (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location +
          2 * (firstSeparation + secondSeparation) / (location - (firstCenter + secondCenter) / 2) ^ 3 +
          3 * ((firstCenter - secondCenter) * (firstSeparation - secondSeparation)) /
            (location - (firstCenter + secondCenter) / 2) ^ 4) := by
    simp only [fourPointExternalPointStrain, star_add, star_div₀, star_mul, star_ofNat, star_pow]
    ring
  rw [identity, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
  convert mul_le_mul_of_nonneg_left estimate (abs_nonneg coefficient) using 1 <;> ring

end EulerNonuniqueness.Section6
