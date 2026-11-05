import EulerNonuniqueness.General.ProjectedQuadraticResonance

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem norm_projected_cubic_error_le
    (projection generator : Space →L[ℝ] Space) (bilinear : BilinearEnd Space)
    (field transverse : Space) {constant : ℝ}
    (fixed : projection transverse = transverse) (linearFixed : projection (generator transverse) = generator transverse)
    (remainderBound : ‖field - generator transverse - bilinear transverse transverse‖ ≤ constant * ‖transverse‖ ^ 3) :
    ‖projection field - generator transverse - projectedQuadratic projection bilinear transverse transverse‖ ≤
      (‖projection‖ * constant) * ‖transverse‖ ^ 3 := by
  have identity : projection field - generator transverse - projectedQuadratic projection bilinear transverse transverse =
      projection (field - generator transverse - bilinear transverse transverse) := by
    change projection field - generator transverse - projection (bilinear (projection transverse) (projection transverse)) = _
    rw [fixed, map_sub, map_sub, linearFixed]
  rw [identity]
  apply (projection.le_opNorm _).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left remainderBound (norm_nonneg projection)

theorem norm_neutral_quadratic_field_le
    (neutral generator : Space →L[ℝ] Space) (bilinear : BilinearEnd Space)
    (field transverse : Space) {constant bilinearBound : ℝ}
    (nonnegative : 0 ≤ constant) (bilinearNonnegative : 0 ≤ bilinearBound)
    (linearZero : neutral (generator transverse) = 0) (small : ‖transverse‖ ≤ 1)
    (bounded : ‖bilinear‖ ≤ bilinearBound)
    (remainderBound : ‖field - generator transverse - bilinear transverse transverse‖ ≤ constant * ‖transverse‖ ^ 3) :
    ‖neutral field‖ ≤ (‖neutral‖ * (constant + bilinearBound)) * ‖transverse‖ ^ 2 := by
  have identity : neutral field = neutral (field - generator transverse - bilinear transverse transverse) +
      neutral (bilinear transverse transverse) := by
    rw [map_sub, map_sub, linearZero]
    abel
  have quadratic : ‖bilinear transverse transverse‖ ≤ bilinearBound * ‖transverse‖ ^ 2 := by
    calc
      _ ≤ ‖bilinear‖ * ‖transverse‖ * ‖transverse‖ := bilinear.le_opNorm₂ _ _
      _ ≤ bilinearBound * ‖transverse‖ * ‖transverse‖ := by gcongr
      _ = _ := by ring
  have cube : ‖transverse‖ ^ 3 ≤ ‖transverse‖ ^ 2 := by
    calc
      _ = ‖transverse‖ * ‖transverse‖ ^ 2 := by ring
      _ ≤ 1 * ‖transverse‖ ^ 2 := mul_le_mul_of_nonneg_right small (sq_nonneg _)
      _ = _ := by ring
  rw [identity]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ ‖neutral‖ * ‖field - generator transverse - bilinear transverse transverse‖ +
        ‖neutral‖ * ‖bilinear transverse transverse‖ :=
      add_le_add (neutral.le_opNorm _) (neutral.le_opNorm _)
    _ ≤ ‖neutral‖ * (constant * ‖transverse‖ ^ 3) + ‖neutral‖ * (bilinearBound * ‖transverse‖ ^ 2) := by
      gcongr
    _ ≤ ‖neutral‖ * (constant * ‖transverse‖ ^ 2) + ‖neutral‖ * (bilinearBound * ‖transverse‖ ^ 2) := by
      gcongr
    _ = _ := by ring

end EulerNonuniqueness.General
