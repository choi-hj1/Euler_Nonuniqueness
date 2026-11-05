import EulerNonuniqueness.General.QuadraticNormalFormForcing

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_frozen_quadratic_remainder_le
    (quadratic correction : BilinearEnd Space) (value remainder forcing : Space)
    {cubicBound quadraticBound correctionBound : ℝ}
    (cubicNonnegative : 0 ≤ cubicBound) (quadraticNonnegative : 0 ≤ quadraticBound)
    (correctionNonnegative : 0 ≤ correctionBound)
    (quadraticNorm : ‖quadratic‖ ≤ quadraticBound) (correctionNorm : ‖correction‖ ≤ correctionBound)
    (small : ‖value‖ ≤ 1) (remainderNorm : ‖remainder‖ ≤ cubicBound * ‖value‖ ^ 3) :
    ‖remainder + forcing -
      (correction (quadratic value value + (remainder + forcing)) value +
        correction value (quadratic value value + (remainder + forcing)))‖ ≤
      (cubicBound + 2 * correctionBound * (quadraticBound + cubicBound)) * ‖value‖ ^ 3 +
        (1 + 2 * correctionBound * ‖value‖) * ‖forcing‖ := by
  have cube : ‖value‖ ^ 3 ≤ ‖value‖ ^ 2 := by
    calc
      _ = ‖value‖ * ‖value‖ ^ 2 := by ring
      _ ≤ 1 * ‖value‖ ^ 2 := mul_le_mul_of_nonneg_right small (sq_nonneg _)
      _ = _ := by ring
  have source : ‖quadratic‖ * ‖value‖ ^ 2 + ‖remainder‖ ≤
      (quadraticBound + cubicBound) * ‖value‖ ^ 2 := by
    calc
      _ ≤ quadraticBound * ‖value‖ ^ 2 + cubicBound * ‖value‖ ^ 3 := by gcongr
      _ ≤ quadraticBound * ‖value‖ ^ 2 + cubicBound * ‖value‖ ^ 2 := by gcongr
      _ = _ := by ring
  have nonlinear := quadraticCoordinate_nonlinear_error_norm_le quadratic correction 1 value remainder
  simp only [one_div_one, one_smul, abs_one, div_one] at nonlinear
  have selfBound :
      ‖remainder - (correction (quadratic value value + remainder) value +
        correction value (quadratic value value + remainder))‖ ≤
        (cubicBound + 2 * correctionBound * (quadraticBound + cubicBound)) * ‖value‖ ^ 3 := by
    apply (norm_sub_le _ _).trans
    apply (add_le_add remainderNorm nonlinear).trans
    calc
      _ ≤ cubicBound * ‖value‖ ^ 3 +
          (2 * correctionBound) * ((quadraticBound + cubicBound) * ‖value‖ ^ 2) * ‖value‖ := by
        gcongr
      _ = _ := by ring
  have forcingBound := quadratic_coordinate_forcing_norm_le correction 1 value forcing
  simp only [one_div_one, one_smul, abs_one, div_one] at forcingBound
  have identity : remainder + forcing -
      (correction (quadratic value value + (remainder + forcing)) value +
        correction value (quadratic value value + (remainder + forcing))) =
      (remainder - (correction (quadratic value value + remainder) value +
        correction value (quadratic value value + remainder))) +
      (forcing - (correction forcing value + correction value forcing)) := by
    simp only [map_add, ContinuousLinearMap.add_apply]
    abel
  rw [identity]
  apply (norm_add_le _ _).trans
  exact add_le_add selfBound (forcingBound.trans (by gcongr))

end EulerNonuniqueness.General
