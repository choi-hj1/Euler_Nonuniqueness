import EulerNonuniqueness.Section6.ActualReceiverStrainError

noncomputable section

namespace EulerNonuniqueness.Section6

theorem exists_reference_strain_projection_bound :
    ∃ radius > (0 : ℝ), ∀ positive negative strain : ℂ,
      positive ≠ 0 → negative ≠ 0 →
      |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| ≤ radius →
      |(pointShapeForcing positive negative (strain * star positive) (strain * star negative)).1| ≤ 5 * ‖strain‖ := by
  obtain ⟨constant, constantNonnegative, radius, radiusPositive, remainder⟩ := pointShapeForcing_strain_remainder
  let smallRadius := min (radius / 2) (1 / (constant + 1))
  have denominatorPositive : 0 < constant + 1 := by positivity
  refine ⟨smallRadius, by dsimp only [smallRadius]; positivity, ?_⟩
  intro positive negative strain positiveNonzero negativeNonzero small
  let size := |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2|
  have sizeSmall : size < radius := (small.trans (min_le_left _ _)).trans_lt (by linarith)
  have coefficient : constant * size ≤ 1 := by
    have sizeNonnegative : 0 ≤ size := by dsimp only [size]; positivity
    have enlarged := mul_le_mul_of_nonneg_right (show constant ≤ constant + 1 by linarith) sizeNonnegative
    have normalized := mul_le_mul_of_nonneg_left (small.trans (min_le_right _ _)) denominatorPositive.le
    have identity : (constant + 1) * (1 / (constant + 1)) = 1 := by field_simp
    rw [identity] at normalized
    exact enlarged.trans normalized
  let logarithmic := strain * star positive / positive
  have logarithmicNorm : ‖logarithmic‖ = ‖strain‖ := by
    dsimp only [logarithmic]
    rw [norm_div, norm_mul, norm_star, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr positiveNonzero)]
  have projection := rhombus_logarithmic_projection_difference logarithmic 0
  simp only [Complex.zero_re, Complex.zero_im, mul_zero, sub_zero] at projection
  rw [logarithmicNorm] at projection
  have actual := remainder positive negative strain positiveNonzero negativeNonzero sizeSmall
  have first := (norm_fst_le
    (pointShapeForcing positive negative (strain * star positive) (strain * star negative) -
      (-2 * logarithmic.re - Real.sqrt 2 * logarithmic.im, -2 * logarithmic.re + Real.sqrt 2 * logarithmic.im))).trans actual
  simp only [Prod.fst_sub, Real.norm_eq_abs] at first
  have triangle := abs_sub_le (pointShapeForcing positive negative (strain * star positive) (strain * star negative)).1
    (-2 * logarithmic.re - Real.sqrt 2 * logarithmic.im) 0
  simp only [sub_zero] at triangle
  have weighted := mul_le_mul_of_nonneg_right coefficient (norm_nonneg strain)
  change |(pointShapeForcing positive negative (strain * star positive) (strain * star negative)).1 -
    (-2 * logarithmic.re - Real.sqrt 2 * logarithmic.im)| ≤ constant * ‖strain‖ * size at first
  have errorBound : constant * ‖strain‖ * size ≤ ‖strain‖ := by nlinarith [weighted]
  exact triangle.trans ((add_le_add (first.trans errorBound) projection).trans (by linarith))

end EulerNonuniqueness.Section6
