import Mathlib

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem mean_component_quadratic_norm_le (relative transverse basis : Space) {mean constant : ℝ}
    (decomposition : relative = transverse + mean • basis)
    (meanBound : |mean| ≤ constant * ‖transverse‖ ^ 2) :
    ‖relative - transverse‖ ≤ (constant * ‖basis‖) * ‖transverse‖ ^ 2 := by
  have identity : relative - transverse = mean • basis := by
    calc
      relative - transverse = (transverse + mean • basis) - transverse :=
        congrArg (fun value => value - transverse) decomposition
      _ = mean • basis := by abel
  rw [identity, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ (constant * ‖transverse‖ ^ 2) * ‖basis‖ :=
      mul_le_mul_of_nonneg_right meanBound (norm_nonneg _)
    _ = _ := by ring

end EulerNonuniqueness.General
