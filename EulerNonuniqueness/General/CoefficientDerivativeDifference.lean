import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic

noncomputable section

namespace EulerNonuniqueness.General

variable {Domain Coefficient Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Coefficient] [NormedSpace ℝ Coefficient]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem coefficient_derivative_difference_norm_le
    (first second : Domain →L[ℝ] Coefficient →L[ℝ] Target)
    (firstVelocity secondVelocity : Domain) (coefficient : Coefficient) :
    ‖first firstVelocity coefficient - second secondVelocity coefficient‖ ≤
      ‖coefficient‖ * (‖first‖ * ‖firstVelocity - secondVelocity‖ +
        ‖first - second‖ * ‖secondVelocity‖) := by
  have applied (operator : Domain →L[ℝ] Coefficient →L[ℝ] Target) (direction : Domain) :
      ‖operator direction coefficient‖ ≤ ‖operator‖ * ‖direction‖ * ‖coefficient‖ :=
    ((operator direction).le_opNorm coefficient).trans
      (mul_le_mul_of_nonneg_right (operator.le_opNorm direction) (norm_nonneg _))
  have equality : first firstVelocity coefficient - second secondVelocity coefficient =
      first (firstVelocity - secondVelocity) coefficient + (first - second) secondVelocity coefficient := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [equality]
  calc
    _ ≤ ‖first (firstVelocity - secondVelocity) coefficient‖ + ‖(first - second) secondVelocity coefficient‖ :=
      norm_add_le _ _
    _ ≤ ‖first‖ * ‖firstVelocity - secondVelocity‖ * ‖coefficient‖ +
        ‖first - second‖ * ‖secondVelocity‖ * ‖coefficient‖ :=
      add_le_add (applied _ _) (applied _ _)
    _ = _ := by ring

end EulerNonuniqueness.General
