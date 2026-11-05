import EulerNonuniqueness.General.QuadraticCubicRemainder
import EulerNonuniqueness.General.QuadraticCoordinateSeparation

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem quadratic_normalForm_remainder_norm_le
    (quadratic correction resonant : BilinearEnd Space) (frequency : ℝ) (value remainder : Space)
    {radius cubicBound : ℝ} (cubicNonnegative : 0 ≤ cubicBound)
    (inside : ‖value‖ ≤ radius) (remainderBound : ‖remainder‖ ≤ cubicBound * ‖value‖ ^ 3)
    (small : (‖correction‖ / |frequency|) * radius ≤ 1 / 2) :
    ‖(remainder - (1 / frequency : ℝ) •
      (correction (quadratic value value + remainder) value + correction value (quadratic value value + remainder))) +
        (resonant value value - resonant (quadraticCoordinate correction frequency value)
          (quadraticCoordinate correction frequency value))‖ ≤
      (cubicBound + (2 * ‖correction‖ / |frequency|) * (‖quadratic‖ + cubicBound * radius) +
        (5 / 2 : ℝ) * ‖resonant‖ * (‖correction‖ / |frequency|)) * ‖value‖ ^ 3 := by
  have comparable := quadraticCoordinate_norm_comparable correction frequency value inside small
  have difference := quadraticCoordinate_sub_norm_le correction frequency value
  rw [norm_sub_rev] at difference
  have resonantBound := quadratic_diagonal_sub_norm_le resonant value (quadraticCoordinate correction frequency value)
  have correctedBound := quadratic_coordinate_cubic_remainder_norm_le quadratic correction frequency value remainder
    cubicNonnegative inside remainderBound
  have resonantEstimate : ‖resonant value value - resonant (quadraticCoordinate correction frequency value)
      (quadraticCoordinate correction frequency value)‖ ≤
        (5 / 2 : ℝ) * ‖resonant‖ * (‖correction‖ / |frequency|) * ‖value‖ ^ 3 := by
    calc
      _ ≤ ‖resonant‖ * (‖value‖ + ‖quadraticCoordinate correction frequency value‖) *
          ‖value - quadraticCoordinate correction frequency value‖ := resonantBound
      _ ≤ ‖resonant‖ * (‖value‖ + (3 / 2 : ℝ) * ‖value‖) *
          ((‖correction‖ / |frequency|) * ‖value‖ ^ 2) := by gcongr; exact comparable.2
      _ = _ := by ring
  exact (norm_add_le _ _).trans (by nlinarith [correctedBound, resonantEstimate])

end EulerNonuniqueness.General
