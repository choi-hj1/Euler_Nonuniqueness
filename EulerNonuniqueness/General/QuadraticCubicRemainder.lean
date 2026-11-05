import EulerNonuniqueness.General.QuadraticCoordinateChange

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem quadratic_coordinate_cubic_remainder_norm_le
    (quadratic correction : BilinearEnd Space) (frequency : ℝ) (value remainder : Space)
    {radius cubicBound : ℝ} (cubicNonnegative : 0 ≤ cubicBound)
    (inside : ‖value‖ ≤ radius) (remainderBound : ‖remainder‖ ≤ cubicBound * ‖value‖ ^ 3) :
    ‖remainder - (1 / frequency : ℝ) •
      (correction (quadratic value value + remainder) value + correction value (quadratic value value + remainder))‖ ≤
        (cubicBound + (2 * ‖correction‖ / |frequency|) * (‖quadratic‖ + cubicBound * radius)) * ‖value‖ ^ 3 := by
  have cubicPower : ‖value‖ ^ 3 ≤ radius * ‖value‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr inside) (sq_nonneg ‖value‖)]
  have sourceBound : ‖quadratic‖ * ‖value‖ ^ 2 + ‖remainder‖ ≤
      (‖quadratic‖ + cubicBound * radius) * ‖value‖ ^ 2 := by
    have estimate := mul_le_mul_of_nonneg_left cubicPower cubicNonnegative
    nlinarith
  have errorBound := quadraticCoordinate_nonlinear_error_norm_le quadratic correction frequency value remainder
  calc
    _ ≤ ‖remainder‖ + ‖(1 / frequency : ℝ) •
        (correction (quadratic value value + remainder) value + correction value (quadratic value value + remainder))‖ :=
      norm_sub_le _ _
    _ ≤ cubicBound * ‖value‖ ^ 3 + (2 * ‖correction‖ / |frequency|) *
        (‖quadratic‖ * ‖value‖ ^ 2 + ‖remainder‖) * ‖value‖ := add_le_add remainderBound errorBound
    _ ≤ cubicBound * ‖value‖ ^ 3 + (2 * ‖correction‖ / |frequency|) *
        ((‖quadratic‖ + cubicBound * radius) * ‖value‖ ^ 2) * ‖value‖ := by
      gcongr
    _ = _ := by ring

theorem quadraticCoordinate_norm_comparable
    (correction : BilinearEnd Space) (frequency : ℝ) (value : Space) {radius : ℝ}
    (inside : ‖value‖ ≤ radius) (small : (‖correction‖ / |frequency|) * radius ≤ 1 / 2) :
    ‖value‖ / 2 ≤ ‖quadraticCoordinate correction frequency value‖ ∧
      ‖quadraticCoordinate correction frequency value‖ ≤ (3 / 2 : ℝ) * ‖value‖ := by
  have coefficientNonnegative : 0 ≤ ‖correction‖ / |frequency| := by positivity
  have coefficientBound := mul_le_mul_of_nonneg_left inside coefficientNonnegative
  have scaledBound := mul_le_mul_of_nonneg_right (coefficientBound.trans small) (norm_nonneg value)
  have difference := quadraticCoordinate_sub_norm_le correction frequency value
  have errorBound : ‖quadraticCoordinate correction frequency value - value‖ ≤ ‖value‖ / 2 := by
    nlinarith
  have forward := norm_sub_norm_le (quadraticCoordinate correction frequency value) value
  have backward := norm_sub_norm_le value (quadraticCoordinate correction frequency value)
  rw [norm_sub_rev] at backward
  constructor <;> nlinarith

end EulerNonuniqueness.General
