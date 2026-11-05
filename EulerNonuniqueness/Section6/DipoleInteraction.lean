import EulerNonuniqueness.Section6.FourPointImpulseControl

noncomputable section

namespace EulerNonuniqueness.Section6

def neutralPairVelocity (coefficient : ℝ) (center separation point : ℂ) : ℂ :=
  Complex.I * (coefficient : ℂ) *
    (1 / star (point - center - separation / 2) - 1 / star (point - center + separation / 2))

theorem neutralPairVelocity_identity (coefficient : ℝ) {center separation point : ℂ}
    (firstNonzero : point - center - separation / 2 ≠ 0)
    (secondNonzero : point - center + separation / 2 ≠ 0) :
    neutralPairVelocity coefficient center separation point =
      Complex.I * (coefficient : ℂ) * star separation /
        (star (point - center - separation / 2) * star (point - center + separation / 2)) := by
  unfold neutralPairVelocity
  have firstStarNonzero := star_ne_zero.mpr firstNonzero
  have secondStarNonzero := star_ne_zero.mpr secondNonzero
  have rational (first second : ℂ) (firstNonzero : first ≠ 0) (secondNonzero : second ≠ 0) :
      1 / first - 1 / second = (second - first) / (first * second) := by
    field_simp <;> ring
  rw [rational _ _ firstStarNonzero secondStarNonzero]
  have difference : star (point - center + separation / 2) - star (point - center - separation / 2) = star separation := by
    simp only [star_add, star_sub, star_div₀, star_mul, star_inv₀, star_one, star_ofNat]
    ring
  rw [difference]
  ring

theorem dipole_shift_lower_bound {displacement sourceOffset targetOffset : ℂ}
    (offsetBound : ‖sourceOffset‖ + ‖targetOffset‖ ≤ ‖displacement‖ / 2) :
    ‖displacement‖ / 2 ≤ ‖displacement + targetOffset - sourceOffset‖ := by
  have offsetNorm := norm_sub_le targetOffset sourceOffset
  have triangle : ‖displacement‖ ≤ ‖displacement + targetOffset - sourceOffset‖ +
      ‖targetOffset - sourceOffset‖ := by
    convert norm_sub_le (displacement + targetOffset - sourceOffset) (targetOffset - sourceOffset) using 1 <;>
      congr 1 <;> ring
  linarith

theorem neutralPairVelocity_norm_bound (coefficient : ℝ) {center separation point : ℂ} {distance : ℝ}
    (distancePositive : 0 < distance)
    (firstDistance : distance / 2 ≤ ‖point - center - separation / 2‖)
    (secondDistance : distance / 2 ≤ ‖point - center + separation / 2‖) :
    ‖neutralPairVelocity coefficient center separation point‖ ≤
      4 * |coefficient| * ‖separation‖ / distance ^ 2 := by
  have firstPositive : 0 < ‖point - center - separation / 2‖ := lt_of_lt_of_le (by positivity) firstDistance
  have secondPositive : 0 < ‖point - center + separation / 2‖ := lt_of_lt_of_le (by positivity) secondDistance
  rw [neutralPairVelocity_identity coefficient (norm_ne_zero_iff.mp firstPositive.ne')
    (norm_ne_zero_iff.mp secondPositive.ne')]
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_star, norm_star, norm_star,
    Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  have denominatorBound : distance ^ 2 / 4 ≤
      ‖point - center - separation / 2‖ * ‖point - center + separation / 2‖ := by
    nlinarith [mul_le_mul firstDistance secondDistance (by positivity : 0 ≤ distance / 2) firstPositive.le]
  have numeratorNonnegative : 0 ≤ |coefficient| * ‖separation‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  calc
    _ ≤ (|coefficient| * ‖separation‖) / (distance ^ 2 / 4) :=
      div_le_div_of_nonneg_left numeratorNonnegative (by positivity) denominatorBound
    _ = _ := by ring

theorem dipole_cross_distances {firstCenter secondCenter firstSeparation secondSeparation : ℂ}
    (separationBound : ‖firstSeparation‖ + ‖secondSeparation‖ ≤ ‖secondCenter - firstCenter‖) :
    ‖secondCenter - firstCenter‖ / 2 ≤ ‖secondCenter + secondSeparation / 2 - firstCenter - firstSeparation / 2‖ ∧
    ‖secondCenter - firstCenter‖ / 2 ≤ ‖secondCenter + secondSeparation / 2 - firstCenter + firstSeparation / 2‖ ∧
    ‖secondCenter - firstCenter‖ / 2 ≤ ‖secondCenter - secondSeparation / 2 - firstCenter - firstSeparation / 2‖ ∧
    ‖secondCenter - firstCenter‖ / 2 ≤ ‖secondCenter - secondSeparation / 2 - firstCenter + firstSeparation / 2‖ := by
  have lower (sourceOffset targetOffset : ℂ)
      (sourceNorm : ‖sourceOffset‖ = ‖firstSeparation‖ / 2)
      (targetNorm : ‖targetOffset‖ = ‖secondSeparation‖ / 2) :
      ‖secondCenter - firstCenter‖ / 2 ≤ ‖secondCenter + targetOffset - firstCenter - sourceOffset‖ := by
    have control := dipole_shift_lower_bound (displacement := secondCenter - firstCenter)
      (sourceOffset := sourceOffset) (targetOffset := targetOffset) (by rw [sourceNorm, targetNorm]; linarith)
    convert control using 1 <;> congr 1 <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lower (firstSeparation / 2) (secondSeparation / 2) (by simp [norm_div]) (by simp [norm_div])
  · simpa only [sub_neg_eq_add] using
      lower (-(firstSeparation / 2)) (secondSeparation / 2) (by simp [norm_div]) (by simp [norm_div])
  · simpa only [← sub_eq_add_neg] using
      lower (firstSeparation / 2) (-(secondSeparation / 2)) (by simp [norm_div]) (by simp [norm_div])
  · simpa only [← sub_eq_add_neg, sub_neg_eq_add] using
      lower (-(firstSeparation / 2)) (-(secondSeparation / 2)) (by simp [norm_div]) (by simp [norm_div])

theorem neutralPairVelocity_difference_identity (coefficient : ℝ)
    {firstCenter secondCenter firstSeparation secondSeparation : ℂ}
    (firstNonzero : secondCenter + secondSeparation / 2 - firstCenter - firstSeparation / 2 ≠ 0)
    (secondNonzero : secondCenter + secondSeparation / 2 - firstCenter + firstSeparation / 2 ≠ 0)
    (thirdNonzero : secondCenter - secondSeparation / 2 - firstCenter - firstSeparation / 2 ≠ 0)
    (fourthNonzero : secondCenter - secondSeparation / 2 - firstCenter + firstSeparation / 2 ≠ 0) :
    neutralPairVelocity coefficient firstCenter firstSeparation (secondCenter + secondSeparation / 2) -
        neutralPairVelocity coefficient firstCenter firstSeparation (secondCenter - secondSeparation / 2) =
      -2 * Complex.I * (coefficient : ℂ) * star firstSeparation * star (secondCenter - firstCenter) * star secondSeparation /
        (star (secondCenter + secondSeparation / 2 - firstCenter - firstSeparation / 2) *
          star (secondCenter + secondSeparation / 2 - firstCenter + firstSeparation / 2) *
          star (secondCenter - secondSeparation / 2 - firstCenter - firstSeparation / 2) *
          star (secondCenter - secondSeparation / 2 - firstCenter + firstSeparation / 2)) := by
  rw [neutralPairVelocity_identity coefficient firstNonzero secondNonzero,
    neutralPairVelocity_identity coefficient thirdNonzero fourthNonzero]
  have firstStarNonzero := star_ne_zero.mpr firstNonzero
  have secondStarNonzero := star_ne_zero.mpr secondNonzero
  have thirdStarNonzero := star_ne_zero.mpr thirdNonzero
  have fourthStarNonzero := star_ne_zero.mpr fourthNonzero
  have rational (numerator first second third fourth : ℂ)
      (firstNonzero : first ≠ 0) (secondNonzero : second ≠ 0)
      (thirdNonzero : third ≠ 0) (fourthNonzero : fourth ≠ 0) :
      numerator / (first * second) - numerator / (third * fourth) =
        numerator * (third * fourth - first * second) / (first * second * third * fourth) := by
    field_simp <;> ring
  rw [rational _ _ _ _ _ firstStarNonzero secondStarNonzero thirdStarNonzero fourthStarNonzero]
  have difference :
      star (secondCenter - secondSeparation / 2 - firstCenter - firstSeparation / 2) *
          star (secondCenter - secondSeparation / 2 - firstCenter + firstSeparation / 2) -
        star (secondCenter + secondSeparation / 2 - firstCenter - firstSeparation / 2) *
          star (secondCenter + secondSeparation / 2 - firstCenter + firstSeparation / 2) =
      -2 * star (secondCenter - firstCenter) * star secondSeparation := by
    simp only [star_add, star_sub, star_div₀, star_mul, star_inv₀, star_one, star_ofNat]
    ring
  rw [difference]
  ring

theorem neutralPairVelocity_average_bound (coefficient : ℝ)
    {firstCenter secondCenter firstSeparation secondSeparation : ℂ}
    (distancePositive : 0 < ‖secondCenter - firstCenter‖)
    (separationBound : ‖firstSeparation‖ + ‖secondSeparation‖ ≤ ‖secondCenter - firstCenter‖) :
    ‖(neutralPairVelocity coefficient firstCenter firstSeparation (secondCenter + secondSeparation / 2) +
        neutralPairVelocity coefficient firstCenter firstSeparation (secondCenter - secondSeparation / 2)) / 2‖ ≤
      4 * |coefficient| * ‖firstSeparation‖ / ‖secondCenter - firstCenter‖ ^ 2 := by
  obtain ⟨firstDistance, secondDistance, thirdDistance, fourthDistance⟩ := dipole_cross_distances separationBound
  have firstControl := neutralPairVelocity_norm_bound coefficient distancePositive firstDistance secondDistance
  have secondControl := neutralPairVelocity_norm_bound coefficient distancePositive thirdDistance fourthDistance
  rw [norm_div, Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  exact (norm_add_le _ _).trans (by linarith)

theorem neutralPairVelocity_relative_bound (coefficient : ℝ)
    {firstCenter secondCenter firstSeparation secondSeparation : ℂ}
    (distancePositive : 0 < ‖secondCenter - firstCenter‖)
    (separationBound : ‖firstSeparation‖ + ‖secondSeparation‖ ≤ ‖secondCenter - firstCenter‖) :
    ‖neutralPairVelocity coefficient firstCenter firstSeparation (secondCenter + secondSeparation / 2) -
        neutralPairVelocity coefficient firstCenter firstSeparation (secondCenter - secondSeparation / 2)‖ ≤
      32 * |coefficient| * ‖firstSeparation‖ * ‖secondSeparation‖ / ‖secondCenter - firstCenter‖ ^ 3 := by
  obtain ⟨firstDistance, secondDistance, thirdDistance, fourthDistance⟩ := dipole_cross_distances separationBound
  have firstNonzero := norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < ‖secondCenter - firstCenter‖ / 2) firstDistance)
  have secondNonzero := norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < ‖secondCenter - firstCenter‖ / 2) secondDistance)
  have thirdNonzero := norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < ‖secondCenter - firstCenter‖ / 2) thirdDistance)
  have fourthNonzero := norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < ‖secondCenter - firstCenter‖ / 2) fourthDistance)
  rw [neutralPairVelocity_difference_identity coefficient firstNonzero secondNonzero thirdNonzero fourthNonzero]
  simp only [norm_div, norm_mul, norm_neg, norm_star, Complex.norm_I, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, mul_one]
  have denominatorBound : ‖secondCenter - firstCenter‖ ^ 4 / 16 ≤
      ‖secondCenter + secondSeparation / 2 - firstCenter - firstSeparation / 2‖ *
        ‖secondCenter + secondSeparation / 2 - firstCenter + firstSeparation / 2‖ *
        ‖secondCenter - secondSeparation / 2 - firstCenter - firstSeparation / 2‖ *
        ‖secondCenter - secondSeparation / 2 - firstCenter + firstSeparation / 2‖ := by
    calc
      _ = (‖secondCenter - firstCenter‖ / 2) * (‖secondCenter - firstCenter‖ / 2) *
          (‖secondCenter - firstCenter‖ / 2) * (‖secondCenter - firstCenter‖ / 2) := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ (2 * |coefficient| * ‖firstSeparation‖ * ‖secondCenter - firstCenter‖ * ‖secondSeparation‖) /
        (‖secondCenter - firstCenter‖ ^ 4 / 16) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) denominatorBound
    _ = _ := by field_simp; ring

end EulerNonuniqueness.Section6
