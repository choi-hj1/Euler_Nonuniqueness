import Mathlib

namespace EulerNonuniqueness.General

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem bilinear_opNorm_le_of_diagonal_ball_two
    (bilinear : Domain →L[ℝ] Domain →L[ℝ] Range) {constant : ℝ}
    (nonnegative : 0 ≤ constant)
    (symmetric : ∀ first second, bilinear first second = bilinear second first)
    (diagonal : ∀ value, ‖value‖ ≤ 2 → ‖bilinear value value‖ ≤ constant) :
    ‖bilinear‖ ≤ constant / 2 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro first firstNorm
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro second secondNorm
  have plusNorm : ‖first + second‖ ≤ 2 := by
    have actual := norm_add_le first second
    rw [firstNorm, secondNorm] at actual
    linarith
  have minusNorm : ‖first - second‖ ≤ 2 := by
    have actual := norm_sub_le first second
    rw [firstNorm, secondNorm] at actual
    linarith
  have polarization : (4 : ℝ) • bilinear first second =
      bilinear (first + second) (first + second) - bilinear (first - second) (first - second) := by
    simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    rw [symmetric second first]
    module
  have estimate := norm_sub_le (bilinear (first + second) (first + second))
    (bilinear (first - second) (first - second))
  rw [← polarization, norm_smul, Real.norm_eq_abs] at estimate
  rw [show |(4 : ℝ)| = 4 by norm_num] at estimate
  have plus := diagonal (first + second) plusNorm
  have minus := diagonal (first - second) minusNorm
  linarith

end EulerNonuniqueness.General
