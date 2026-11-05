import EulerNonuniqueness.Section6.SourcePacketReferenceProjectionBound
import EulerNonuniqueness.Section6.SourcePacketPhysicalComparison

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Section6

theorem rhombus_logarithmic_projection_norm_le (value : ℂ) :
    ‖(-2 * value.re - Real.sqrt 2 * value.im, -2 * value.re + Real.sqrt 2 * value.im)‖ ≤ 4 * ‖value‖ := by
  have first := rhombus_logarithmic_projection_difference value 0
  simp only [Complex.zero_re, Complex.zero_im, mul_zero, sub_zero] at first
  have sqrtUpper : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  refine max_le first ?_
  have triangle := abs_add (-2 * value.re) (Real.sqrt 2 * value.im)
  simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ))] at triangle
  nlinarith [Complex.abs_re_le_norm value, Complex.abs_im_le_norm value,
    mul_le_mul sqrtUpper (Complex.abs_im_le_norm value) (abs_nonneg value.im) (by norm_num : (0 : ℝ) ≤ 2)]

theorem exists_reference_strain_vector_projection_bound :
    ∃ radius > (0 : ℝ), ∀ positive negative strain : ℂ,
      positive ≠ 0 → negative ≠ 0 →
      |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| ≤ radius →
      ‖pointShapeForcing positive negative (strain * star positive) (strain * star negative)‖ ≤ 5 * ‖strain‖ := by
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
  have actual := remainder positive negative strain positiveNonzero negativeNonzero sizeSmall
  have weighted := mul_le_mul_of_nonneg_right coefficient (norm_nonneg strain)
  have remainderBound : ‖pointShapeForcing positive negative (strain * star positive) (strain * star negative) -
      (-2 * logarithmic.re - Real.sqrt 2 * logarithmic.im, -2 * logarithmic.re + Real.sqrt 2 * logarithmic.im)‖ ≤ ‖strain‖ := by
    apply actual.trans
    change constant * ‖strain‖ * size ≤ ‖strain‖
    nlinarith
  have projection := rhombus_logarithmic_projection_norm_le logarithmic
  rw [logarithmicNorm] at projection
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (pointShapeForcing positive negative (strain * star positive) (strain * star negative))
    (-2 * logarithmic.re - Real.sqrt 2 * logarithmic.im, -2 * logarithmic.re + Real.sqrt 2 * logarithmic.im) 0
  simp only [sub_zero] at triangle
  exact triangle.trans ((add_le_add remainderBound projection).trans_eq (by ring))

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem measurable_pointShapeForcing_vector {positive negative positiveForcing negativeForcing : ℝ → ℂ}
    (positiveMeasurable : Measurable positive) (negativeMeasurable : Measurable negative)
    (firstMeasurable : Measurable positiveForcing) (secondMeasurable : Measurable negativeForcing) :
    Measurable (fun elapsed => pointShapeForcing (positive elapsed) (negative elapsed)
      (positiveForcing elapsed) (negativeForcing elapsed)) := by
  have difference := (secondMeasurable.div negativeMeasurable).sub (firstMeasurable.div positiveMeasurable)
  have ratio := (negativeMeasurable.norm.pow_const (2 : ℕ)).div (positiveMeasurable.norm.pow_const (2 : ℕ))
  exact (measurable_pointShapeForcing_first positiveMeasurable negativeMeasurable firstMeasurable secondMeasurable).prodMk
    (((((measurable_const.mul ratio).mul difference.re).div_const _).sub
      ((measurable_const.mul difference.im).div_const _)).div_const _)

end EulerNonuniqueness.Paper
