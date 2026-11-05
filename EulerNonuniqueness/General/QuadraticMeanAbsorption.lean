import Mathlib

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem quadratic_mean_absorption
    (relative transverse basis : Space) (mean constant : ℝ)
    (nonnegative : 0 ≤ constant)
    (decomposition : relative = transverse + mean • basis)
    (meanBound : |mean| ≤ constant * ‖relative‖ ^ 2)
    (small : constant * ‖basis‖ * ‖relative‖ ≤ 1 / 2) :
    ‖relative‖ ≤ 2 * ‖transverse‖ ∧
      |mean| ≤ (4 * constant) * ‖transverse‖ ^ 2 := by
  have remainder : ‖mean • basis‖ ≤ ‖relative‖ / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |mean| * ‖basis‖ ≤ (constant * ‖relative‖ ^ 2) * ‖basis‖ :=
        mul_le_mul_of_nonneg_right meanBound (norm_nonneg _)
      _ = (constant * ‖basis‖ * ‖relative‖) * ‖relative‖ := by ring
      _ ≤ (1 / 2) * ‖relative‖ := mul_le_mul_of_nonneg_right small (norm_nonneg _)
      _ = ‖relative‖ / 2 := by ring
  have triangle : ‖relative‖ ≤ ‖transverse‖ + ‖mean • basis‖ := by
    conv_lhs => rw [decomposition]
    exact norm_add_le _ _
  have bound : ‖relative‖ ≤ 2 * ‖transverse‖ := by linarith
  refine ⟨bound, meanBound.trans ?_⟩
  have squared : ‖relative‖ ^ 2 ≤ 4 * ‖transverse‖ ^ 2 := by
    nlinarith [norm_nonneg relative, norm_nonneg transverse]
  nlinarith [mul_le_mul_of_nonneg_left squared nonnegative]

end EulerNonuniqueness.General
