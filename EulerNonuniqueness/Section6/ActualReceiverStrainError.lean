import EulerNonuniqueness.Section6.StrainShapeForcing

noncomputable section

namespace EulerNonuniqueness.Section6

theorem rhombus_logarithmic_projection_difference (first second : ℂ) :
    |(-2 * first.re - Real.sqrt 2 * first.im) - (-2 * second.re - Real.sqrt 2 * second.im)| ≤
      4 * ‖first - second‖ := by
  have identity : (-2 * first.re - Real.sqrt 2 * first.im) - (-2 * second.re - Real.sqrt 2 * second.im) =
      -2 * (first - second).re - Real.sqrt 2 * (first - second).im := by
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have sqrtUpper : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  rw [identity]
  calc
    _ ≤ 2 * |(first - second).re| + Real.sqrt 2 * |(first - second).im| := by
      simpa only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ))] using
        abs_sub (-2 * (first - second).re) (Real.sqrt 2 * (first - second).im)
    _ ≤ 2 * ‖first - second‖ + 2 * ‖first - second‖ := by
      exact add_le_add (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num))
        (mul_le_mul sqrtUpper (Complex.abs_im_le_norm _) (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem actual_receiver_strain_error :
    ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
    ∀ positive negative idealPositive actualStrain modelStrain : ℂ,
      positive ≠ 0 → negative ≠ 0 → idealPositive ≠ 0 →
      |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| < radius →
      |(pointShapeForcing positive negative (actualStrain * star positive) (actualStrain * star negative)).1 -
        (pointShapeForcing idealPositive
          (Complex.I * (Real.sqrt Section2.rhombusRatio : ℂ) * idealPositive)
          (modelStrain * star idealPositive)
          (modelStrain * star (Complex.I * (Real.sqrt Section2.rhombusRatio : ℂ) * idealPositive))).1| ≤
        constant * ‖actualStrain‖ *
          (|(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2|) +
          4 * ‖actualStrain - modelStrain‖ +
          4 * ‖modelStrain‖ * ‖star positive / positive - star idealPositive / idealPositive‖ := by
  obtain ⟨constant, constantNonnegative, radius, radiusPositive, remainderBound⟩ := pointShapeForcing_strain_remainder
  refine ⟨constant, constantNonnegative, radius, radiusPositive, ?_⟩
  intro positive negative idealPositive actualStrain modelStrain positiveNonzero negativeNonzero idealNonzero small
  have remainder := remainderBound positive negative actualStrain positiveNonzero negativeNonzero small
  dsimp only at remainder
  have component : |(pointShapeForcing positive negative
        (actualStrain * star positive) (actualStrain * star negative)).1 -
        (-2 * (actualStrain * star positive / positive).re -
          Real.sqrt 2 * (actualStrain * star positive / positive).im)| ≤
      constant * ‖actualStrain‖ *
        (|(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2|) := by
    have projected := norm_fst_le (pointShapeForcing positive negative (actualStrain * star positive) (actualStrain * star negative) -
        (-2 * (actualStrain * star positive / positive).re - Real.sqrt 2 * (actualStrain * star positive / positive).im,
          -2 * (actualStrain * star positive / positive).re + Real.sqrt 2 * (actualStrain * star positive / positive).im))
    exact (by simpa only [Prod.fst_sub, Real.norm_eq_abs] using projected.trans remainder)
  have logarithmicIdentity : actualStrain * star positive / positive - modelStrain * star idealPositive / idealPositive =
      (actualStrain - modelStrain) * (star positive / positive) +
        modelStrain * (star positive / positive - star idealPositive / idealPositive) := by ring
  have quotientNorm : ‖star positive / positive‖ = 1 := by
    rw [norm_div, norm_star, div_self (norm_ne_zero_iff.mpr positiveNonzero)]
  have logarithmicBound : ‖actualStrain * star positive / positive - modelStrain * star idealPositive / idealPositive‖ ≤
      ‖actualStrain - modelStrain‖ + ‖modelStrain‖ * ‖star positive / positive - star idealPositive / idealPositive‖ := by
    rw [logarithmicIdentity]
    simpa only [norm_mul, quotientNorm, mul_one] using
      norm_add_le ((actualStrain - modelStrain) * (star positive / positive))
        (modelStrain * (star positive / positive - star idealPositive / idealPositive))
  have projection := (rhombus_logarithmic_projection_difference
    (actualStrain * star positive / positive) (modelStrain * star idealPositive / idealPositive)).trans
      (mul_le_mul_of_nonneg_left logarithmicBound (by norm_num : (0 : ℝ) ≤ 4))
  rw [pointShapeForcing_rhombus idealNonzero]
  dsimp only
  have triangle := abs_sub_le
    (pointShapeForcing positive negative (actualStrain * star positive) (actualStrain * star negative)).1
    (-2 * (actualStrain * star positive / positive).re - Real.sqrt 2 * (actualStrain * star positive / positive).im)
    (-2 * (modelStrain * star idealPositive / idealPositive).re - Real.sqrt 2 * (modelStrain * star idealPositive / idealPositive).im)
  exact triangle.trans ((add_le_add component projection).trans_eq (by ring))

end EulerNonuniqueness.Section6
