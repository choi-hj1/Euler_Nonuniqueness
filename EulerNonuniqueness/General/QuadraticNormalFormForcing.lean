import EulerNonuniqueness.General.QuadraticNormalFormRemainder

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem quadratic_coordinate_forcing_norm_le
    (correction : BilinearEnd Space) (frequency : ℝ) (value forcing : Space) :
    ‖forcing - (1 / frequency : ℝ) • (correction forcing value + correction value forcing)‖ ≤
      (1 + (2 * ‖correction‖ / |frequency|) * ‖value‖) * ‖forcing‖ := by
  have paired : ‖correction forcing value + correction value forcing‖ ≤
      2 * ‖correction‖ * ‖value‖ * ‖forcing‖ := by
    calc
      _ ≤ ‖correction forcing value‖ + ‖correction value forcing‖ := norm_add_le _ _
      _ ≤ ‖correction‖ * ‖forcing‖ * ‖value‖ + ‖correction‖ * ‖value‖ * ‖forcing‖ :=
        add_le_add (correction.le_opNorm₂ _ _) (correction.le_opNorm₂ _ _)
      _ = _ := by ring
  calc
    _ ≤ ‖forcing‖ + ‖(1 / frequency : ℝ) • (correction forcing value + correction value forcing)‖ := norm_sub_le _ _
    _ = ‖forcing‖ + (1 / |frequency|) * ‖correction forcing value + correction value forcing‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_one]
    _ ≤ ‖forcing‖ + (1 / |frequency|) * (2 * ‖correction‖ * ‖value‖ * ‖forcing‖) := by gcongr
    _ = _ := by ring

theorem quadratic_coordinate_forced_remainder_norm_le
    (quadratic correction resonant : BilinearEnd Space) (frequency : ℝ) (value remainder forcing : Space)
    {radius cubicBound : ℝ} (cubicNonnegative : 0 ≤ cubicBound)
    (inside : ‖value‖ ≤ radius) (remainderBound : ‖remainder‖ ≤ cubicBound * ‖value‖ ^ 3)
    (small : (‖correction‖ / |frequency|) * radius ≤ 1 / 2) :
    ‖(remainder + forcing - (1 / frequency : ℝ) •
      (correction (quadratic value value + (remainder + forcing)) value +
        correction value (quadratic value value + (remainder + forcing)))) +
          (resonant value value - resonant (quadraticCoordinate correction frequency value)
            (quadraticCoordinate correction frequency value))‖ ≤
      (cubicBound + (2 * ‖correction‖ / |frequency|) * (‖quadratic‖ + cubicBound * radius) +
        (5 / 2 : ℝ) * ‖resonant‖ * (‖correction‖ / |frequency|)) * ‖value‖ ^ 3 +
          (1 + (2 * ‖correction‖ / |frequency|) * radius) * ‖forcing‖ := by
  have decomposition :
      (remainder + forcing - (1 / frequency : ℝ) •
        (correction (quadratic value value + (remainder + forcing)) value +
          correction value (quadratic value value + (remainder + forcing)))) +
            (resonant value value - resonant (quadraticCoordinate correction frequency value)
              (quadraticCoordinate correction frequency value)) =
      ((remainder - (1 / frequency : ℝ) •
        (correction (quadratic value value + remainder) value + correction value (quadratic value value + remainder))) +
          (resonant value value - resonant (quadraticCoordinate correction frequency value)
            (quadraticCoordinate correction frequency value))) +
      (forcing - (1 / frequency : ℝ) • (correction forcing value + correction value forcing)) := by
    simp only [map_add, ContinuousLinearMap.add_apply, smul_add]
    abel
  rw [decomposition]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact quadratic_normalForm_remainder_norm_le quadratic correction resonant frequency value remainder
      cubicNonnegative inside remainderBound small
  · exact (quadratic_coordinate_forcing_norm_le correction frequency value forcing).trans (by gcongr)

end EulerNonuniqueness.General
