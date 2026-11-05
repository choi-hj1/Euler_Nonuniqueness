import EulerNonuniqueness.Section6.RelativeShapeForcingOperator

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

def shapeLogProjection (ratio : ℝ) (value : ℂ) : ℝ × ℝ :=
  (ratio * value.re + value.im / Real.sqrt 2, ratio * value.re - value.im / Real.sqrt 2)

theorem shapeLogProjection_norm_le (ratio : ℝ) (value : ℂ) (nonnegative : 0 ≤ ratio) :
    ‖shapeLogProjection ratio value‖ ≤ (ratio + 1) * ‖value‖ := by
  have imaginary : |value.im| / Real.sqrt 2 ≤ ‖value‖ :=
    (div_le_self (abs_nonneg _) (by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)] : 1 ≤ Real.sqrt 2)).trans
      (Complex.abs_im_le_norm value)
  have realPart := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm value) nonnegative
  rw [shapeLogProjection, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  apply max_le
  · have triangle := abs_add (ratio * value.re) (value.im / Real.sqrt 2)
    rw [abs_mul, abs_of_nonneg nonnegative, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)] at triangle
    nlinarith only [triangle, realPart, imaginary]
  · have triangle := abs_sub (ratio * value.re) (value.im / Real.sqrt 2)
    rw [abs_mul, abs_of_nonneg nonnegative, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)] at triangle
    nlinarith only [triangle, realPart, imaginary]

theorem shapeLogProjection_relative_bound (firstRatio secondRatio : ℝ) (first second : ℂ)
    (nonnegative : 0 ≤ firstRatio) :
    ‖shapeLogProjection firstRatio first - shapeLogProjection secondRatio second‖ ≤
      (firstRatio + 1) * ‖first - second‖ + |firstRatio - secondRatio| * ‖second‖ := by
  have identity : shapeLogProjection firstRatio first - shapeLogProjection secondRatio second =
      shapeLogProjection firstRatio (first - second) +
        ((firstRatio - secondRatio) * second.re, (firstRatio - secondRatio) * second.re) := by
    ext <;> simp only [shapeLogProjection, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Complex.sub_re, Complex.sub_im] <;> ring
  rw [identity]
  apply (norm_add_le _ _).trans
  apply add_le_add (shapeLogProjection_norm_le _ _ nonnegative)
  simp only [Prod.norm_def, Real.norm_eq_abs, max_self, abs_mul]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm second) (abs_nonneg _)

theorem pointShapeForcingCLM_eq_logProjection (point forcing : ℂ × ℂ) :
    pointShapeForcingCLM point forcing = shapeLogProjection (pointShapeRatio point.1 point.2 / rhombusRatio)
      (forcing.2 / point.2 - forcing.1 / point.1) := by
  rw [pointShapeForcingCLM_apply]
  ext <;> dsimp only [pointShapeForcing, shapeLogProjection] <;> ring

def pointShapeForcingOperatorVariation (first second : ℂ × ℂ) : ℝ :=
  (pointShapeRatio first.1 first.2 / rhombusRatio + 1) *
      (‖first.2⁻¹ - second.2⁻¹‖ + ‖first.1⁻¹ - second.1⁻¹‖) +
    |pointShapeRatio first.1 first.2 / rhombusRatio - pointShapeRatio second.1 second.2 / rhombusRatio| *
      (‖second.2⁻¹‖ + ‖second.1⁻¹‖)

theorem pointShapeForcingOperatorVariation_nonnegative (first second : ℂ × ℂ) :
    0 ≤ pointShapeForcingOperatorVariation first second := by
  have rhombusPositive := rhombusRatio_pos
  dsimp only [pointShapeForcingOperatorVariation, pointShapeRatio]
  positivity

theorem pointShapeForcingCLM_difference_norm_le (first second : ℂ × ℂ) :
    ‖pointShapeForcingCLM first - pointShapeForcingCLM second‖ ≤ pointShapeForcingOperatorVariation first second := by
  apply ContinuousLinearMap.opNorm_le_bound _ (pointShapeForcingOperatorVariation_nonnegative first second)
  intro forcing
  simp only [ContinuousLinearMap.sub_apply, pointShapeForcingCLM_eq_logProjection]
  have ratioNonnegative : 0 ≤ pointShapeRatio first.1 first.2 / rhombusRatio := by
    have rhombusPositive := rhombusRatio_pos
    dsimp only [pointShapeRatio]
    positivity
  have main := shapeLogProjection_relative_bound (pointShapeRatio first.1 first.2 / rhombusRatio)
    (pointShapeRatio second.1 second.2 / rhombusRatio) (forcing.2 / first.2 - forcing.1 / first.1)
    (forcing.2 / second.2 - forcing.1 / second.1) ratioNonnegative
  have identity : (forcing.2 / first.2 - forcing.1 / first.1) - (forcing.2 / second.2 - forcing.1 / second.1) =
      forcing.2 * (first.2⁻¹ - second.2⁻¹) - forcing.1 * (first.1⁻¹ - second.1⁻¹) := by
    simp only [div_eq_mul_inv]
    ring
  have difference : ‖(forcing.2 / first.2 - forcing.1 / first.1) - (forcing.2 / second.2 - forcing.1 / second.1)‖ ≤
      (‖first.2⁻¹ - second.2⁻¹‖ + ‖first.1⁻¹ - second.1⁻¹‖) * ‖forcing‖ := by
    rw [identity]
    apply (norm_sub_le _ _).trans
    rw [norm_mul, norm_mul]
    have enlarged := add_le_add (mul_le_mul_of_nonneg_right (norm_snd_le forcing) (norm_nonneg (first.2⁻¹ - second.2⁻¹)))
      (mul_le_mul_of_nonneg_right (norm_fst_le forcing) (norm_nonneg (first.1⁻¹ - second.1⁻¹)))
    exact enlarged.trans_eq (by ring)
  have secondBound : ‖forcing.2 / second.2 - forcing.1 / second.1‖ ≤ (‖second.2⁻¹‖ + ‖second.1⁻¹‖) * ‖forcing‖ := by
    apply (norm_sub_le _ _).trans
    simp only [div_eq_mul_inv, norm_mul]
    have enlarged := add_le_add (mul_le_mul_of_nonneg_right (norm_snd_le forcing) (norm_nonneg second.2⁻¹))
      (mul_le_mul_of_nonneg_right (norm_fst_le forcing) (norm_nonneg second.1⁻¹))
    exact enlarged.trans_eq (by ring)
  apply main.trans
  have enlarged := add_le_add (mul_le_mul_of_nonneg_left difference (add_nonneg ratioNonnegative zero_le_one))
    (mul_le_mul_of_nonneg_left secondBound (abs_nonneg
      (pointShapeRatio first.1 first.2 / rhombusRatio - pointShapeRatio second.1 second.2 / rhombusRatio)))
  exact enlarged.trans_eq (by dsimp only [pointShapeForcingOperatorVariation]; ring)

end EulerNonuniqueness.Section6
