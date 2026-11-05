import EulerNonuniqueness.General.ProjectedNeutralCubicBounds

namespace EulerNonuniqueness.General

variable {Space Parameter : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem norm_projected_quadratic_family_cubic_le
    (projection generator : Space →L[ℝ] Space)
    (bilinear projected : Parameter → BilinearEnd Space)
    (projectedApply : ∀ parameter first second, projected parameter first second =
      projection (bilinear parameter (projection first) (projection second)))
    (linearFixed : ∀ value, projection (generator value) = generator value)
    (parameter : Parameter) (field transverse : Space) {constant : ℝ}
    (fixed : projection transverse = transverse)
    (remainderBound : ‖field - generator transverse - bilinear parameter transverse transverse‖ ≤
      constant * ‖transverse‖ ^ 3) :
    ‖projection field - generator transverse - projected parameter transverse transverse‖ ≤
      (‖projection‖ * constant) * ‖transverse‖ ^ 3 := by
  have identity : projected parameter = projectedQuadratic projection (bilinear parameter) := by
    ext first second
    exact projectedApply parameter first second
  rw [identity]
  exact norm_projected_cubic_error_le projection generator (bilinear parameter) field transverse
    fixed (linearFixed transverse) remainderBound

theorem norm_neutral_quadratic_family_field_le
    (neutral generator : Space →L[ℝ] Space) (bilinear : Parameter → BilinearEnd Space)
    (linearZero : ∀ value, neutral (generator value) = 0)
    (parameter : Parameter) (field transverse : Space) {constant bilinearBound : ℝ}
    (nonnegative : 0 ≤ constant) (bilinearNonnegative : 0 ≤ bilinearBound)
    (small : ‖transverse‖ ≤ 1) (bounded : ‖bilinear parameter‖ ≤ bilinearBound)
    (remainderBound : ‖field - generator transverse - bilinear parameter transverse transverse‖ ≤
      constant * ‖transverse‖ ^ 3) :
    ‖neutral field‖ ≤ (‖neutral‖ * (constant + bilinearBound)) * ‖transverse‖ ^ 2 := by
  exact norm_neutral_quadratic_field_le neutral generator (bilinear parameter) field transverse
    nonnegative bilinearNonnegative (linearZero transverse) small bounded remainderBound

end EulerNonuniqueness.General
