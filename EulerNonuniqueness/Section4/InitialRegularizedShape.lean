import EulerNonuniqueness.Section4.InitialReferenceShapeCoordinates
import EulerNonuniqueness.Section4.RegularizedShapeCoordinates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section

namespace EulerNonuniqueness.Paper

theorem initialDiagonals_ratio_im_lower (scales : Scales) (index : ℕ) (phase unstable : ℝ)
    (small : |unstable| ≤ 1 / 2) :
    1 / 8 ≤ (initialNegativeDiagonal scales index phase unstable /
      initialPositiveDiagonal scales index phase unstable).im := by
  have ratioLower : (1 / 16 : ℝ) ≤ rhombusRatio * (1 + unstable) := by
    nlinarith [reference_rhombusRatio_lower, (abs_le.mp small).1]
  have rootLower : (1 / 4 : ℝ) ≤ Real.sqrt (rhombusRatio * (1 + unstable)) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have sqrtPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have sqrtLower : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have displacement : |unstable / Real.sqrt 2| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos sqrtPositive]
    exact (div_le_iff₀ sqrtPositive).mpr (by nlinarith)
  have square : (unstable / Real.sqrt 2) ^ 2 ≤ 1 / 4 := by
    nlinarith [(abs_le.mp displacement).1, (abs_le.mp displacement).2]
  have cosine : (1 / 2 : ℝ) ≤ Real.cos (unstable / Real.sqrt 2) := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := unstable / Real.sqrt 2)]
  have exponential : Complex.exp (Complex.I * (Real.pi / 2 + unstable / Real.sqrt 2 : ℝ)) =
      (Real.cos (Real.pi / 2 + unstable / Real.sqrt 2) : ℂ) +
        (Real.sin (Real.pi / 2 + unstable / Real.sqrt 2) : ℂ) * Complex.I := by
    rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [initialDiagonals_ratio scales index phase unstable small, exponential]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.mul_re,
    Complex.I_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one]
  rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two, one_mul, zero_mul, add_zero]
  nlinarith

theorem initialDiagonals_regularizedShape_eq (scales : Scales) (index : ℕ) (phase unstable : ℝ)
    (small : |unstable| ≤ 1 / 2) :
    regularizedShapeCoordinates (scales.length index ^ 2 / 2) (1 / 16)
      (initialPositiveDiagonal scales index phase unstable) (initialNegativeDiagonal scales index phase unstable) =
        (unstable, 0) := by
  have normLower := (initialDiagonals_separation_bounds scales index phase unstable small).1
  have denominatorLower : scales.length index ^ 2 / 2 ≤ ‖initialPositiveDiagonal scales index phase unstable‖ ^ 2 := by
    have lengthPositive := scales.length_pos index
    nlinarith
  have imaginaryLower : (1 / 16 : ℝ) ≤
      (initialNegativeDiagonal scales index phase unstable / initialPositiveDiagonal scales index phase unstable).im := by
    linarith [initialDiagonals_ratio_im_lower scales index phase unstable small]
  have actual := (initialDiagonals_upper_and_shape scales index phase unstable small).2
  rw [Section6.pointShapeChart,
    Section6.pointShapeAngle_eq_twice_arg_of_upper (initialDiagonals_upper_and_shape scales index phase unstable small).1] at actual
  unfold regularizedShapeCoordinates
  rw [max_eq_right denominatorLower, regularizedDiagonalRatio_eq_of_lower_bound denominatorLower,
    upperHalfPlaneClamp_eq_of_lower_bound imaginaryLower]
  simpa only [Section6.shapeChart, Section6.pointShapeRatio,
    div_sub_one Section2.rhombusRatio_pos.ne'] using actual

end EulerNonuniqueness.Paper
