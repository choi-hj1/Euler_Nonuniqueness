import EulerNonuniqueness.Section6.PointSourceDifferentiation

noncomputable section

namespace EulerNonuniqueness.Section6

theorem twoDipole_physical_strain_moment_error (coefficient : ℝ)
    {firstCenter secondCenter firstSeparation secondSeparation location : ℂ} {length : ℝ}
    (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (separated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (far : ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2)
    (modelMoment : ℂ) :
    ‖fourPointExternalPointStrain coefficient
        (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location -
      (-3 * Complex.I * (coefficient : ℂ) * star modelMoment /
        star (location - (firstCenter + secondCenter) / 2) ^ 4)‖ ≤
      2 * |coefficient| * ‖firstSeparation + secondSeparation‖ /
          ‖location - (firstCenter + secondCenter) / 2‖ ^ 3 +
        3 * |coefficient| * ‖(firstCenter - secondCenter) * (firstSeparation - secondSeparation) - modelMoment‖ /
          ‖location - (firstCenter + secondCenter) / 2‖ ^ 4 +
        704 * |coefficient| * ‖firstCenter - secondCenter‖ ^ 2 * length /
          ‖location - (firstCenter + secondCenter) / 2‖ ^ 5 := by
  let displacement := location - (firstCenter + secondCenter) / 2
  let moment := (firstCenter - secondCenter) * (firstSeparation - secondSeparation)
  let field := fourPointExternalPointStrain coefficient
    (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location
  have estimate := twoDipole_physical_strain_far_field coefficient lengthPositive firstBound secondBound separated far
  have identity : field - (-3 * Complex.I * (coefficient : ℂ) * star modelMoment / star displacement ^ 4) =
      -(2 * Complex.I * (coefficient : ℂ) * star (firstSeparation + secondSeparation) / star displacement ^ 3) -
        3 * Complex.I * (coefficient : ℂ) * star (moment - modelMoment) / star displacement ^ 4 +
        (field + 2 * Complex.I * (coefficient : ℂ) * star (firstSeparation + secondSeparation) / star displacement ^ 3 +
          3 * Complex.I * (coefficient : ℂ) * star moment / star displacement ^ 4) := by
    rw [star_sub moment modelMoment]
    ring
  rw [identity]
  apply (norm_add_le _ _).trans
  apply add_le_add _ estimate
  apply (norm_sub_le _ _).trans
  simp only [norm_neg, norm_div, norm_mul, norm_pow, norm_star, Complex.norm_ofNat, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, mul_one]
  dsimp [displacement, moment]
  ring_nf
  exact le_rfl

theorem rhombus_unstable_strain_lipschitz {positive : ℂ} (positiveNonzero : positive ≠ 0)
    (firstStrain secondStrain : ℂ) :
    |(pointShapeForcing positive (Complex.I * (Real.sqrt EulerNonuniqueness.Section2.rhombusRatio : ℂ) * positive)
        (firstStrain * star positive)
        (firstStrain * star (Complex.I * (Real.sqrt EulerNonuniqueness.Section2.rhombusRatio : ℂ) * positive))).1 -
      (pointShapeForcing positive (Complex.I * (Real.sqrt EulerNonuniqueness.Section2.rhombusRatio : ℂ) * positive)
        (secondStrain * star positive)
        (secondStrain * star (Complex.I * (Real.sqrt EulerNonuniqueness.Section2.rhombusRatio : ℂ) * positive))).1| ≤
      4 * ‖firstStrain - secondStrain‖ := by
  rw [pointShapeForcing_rhombus positiveNonzero, pointShapeForcing_rhombus positiveNonzero]
  dsimp only
  let difference := (firstStrain - secondStrain) * star positive / positive
  have identity : (-2 * (firstStrain * star positive / positive).re - Real.sqrt 2 * (firstStrain * star positive / positive).im) -
      (-2 * (secondStrain * star positive / positive).re - Real.sqrt 2 * (secondStrain * star positive / positive).im) =
      -2 * difference.re - Real.sqrt 2 * difference.im := by
    dsimp [difference]
    rw [sub_mul, sub_div, Complex.sub_re, Complex.sub_im]
    ring
  have differenceNorm : ‖difference‖ = ‖firstStrain - secondStrain‖ := by
    dsimp [difference]
    rw [norm_div, norm_mul]
    simp only [← Complex.star_def, norm_star]
    exact mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr positiveNonzero)
  have sqrtUpper : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  rw [identity]
  calc
    _ ≤ 2 * |difference.re| + Real.sqrt 2 * |difference.im| := by
      simpa only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ))] using
        abs_sub (-2 * difference.re) (Real.sqrt 2 * difference.im)
    _ ≤ 2 * ‖difference‖ + 2 * ‖difference‖ := by
      gcongr
      · exact Complex.abs_re_le_norm difference
      · exact Complex.abs_im_le_norm difference
    _ = _ := by rw [differenceNorm]; ring

end EulerNonuniqueness.Section6
