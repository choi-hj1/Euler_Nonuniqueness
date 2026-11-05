import EulerNonuniqueness.General.QuadraticCoordinateSeparation

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem projected_quadratic_bound_of_neutral_cancellation
    (bilinear : BilinearEnd Space) (projection : Space →L[ℝ] Space)
    (neutral relative transverse : Space)
    (leftNeutral : ∀ value, bilinear neutral value = 0)
    (rightNeutral : ∀ value, bilinear value neutral = 0)
    (transverseZero : projection (bilinear transverse transverse) = 0)
    (relativeBound : ‖relative‖ ≤ 2 * ‖transverse‖) :
    ‖projection (bilinear (neutral + relative) (neutral + relative))‖ ≤
      3 * ‖projection‖ * ‖bilinear‖ * ‖transverse‖ * ‖relative - transverse‖ := by
  have cancellation : bilinear (neutral + relative) (neutral + relative) = bilinear relative relative := by
    simp only [map_add, ContinuousLinearMap.add_apply, leftNeutral, rightNeutral, zero_add, add_zero]
  have projectedDifference : projection (bilinear relative relative) =
      projection (bilinear relative relative - bilinear transverse transverse) := by
    rw [map_sub, transverseZero, sub_zero]
  rw [cancellation, projectedDifference]
  calc
    _ ≤ ‖projection‖ * ‖bilinear relative relative - bilinear transverse transverse‖ := projection.le_opNorm _
    _ ≤ ‖projection‖ * (‖bilinear‖ * (‖relative‖ + ‖transverse‖) * ‖relative - transverse‖) :=
      mul_le_mul_of_nonneg_left (quadratic_diagonal_sub_norm_le bilinear relative transverse) (norm_nonneg _)
    _ ≤ ‖projection‖ * (‖bilinear‖ * (2 * ‖transverse‖ + ‖transverse‖) * ‖relative - transverse‖) := by
      gcongr
    _ = _ := by ring

theorem projected_quadratic_cubic_factor_of_mean_defect
    (bilinear : BilinearEnd Space) (projection : Space →L[ℝ] Space)
    (neutral relative transverse : Space) {constant size : ℝ}
    (leftNeutral : ∀ value, bilinear neutral value = 0)
    (rightNeutral : ∀ value, bilinear value neutral = 0)
    (transverseZero : projection (bilinear transverse transverse) = 0)
    (relativeBound : ‖relative‖ ≤ 2 * ‖transverse‖)
    (meanBound : ‖relative - transverse‖ ≤ constant * size * ‖transverse‖) :
    ‖projection (bilinear (neutral + relative) (neutral + relative))‖ ≤
      (3 * ‖projection‖ * ‖bilinear‖ * constant) * size * ‖transverse‖ ^ 2 := by
  exact (projected_quadratic_bound_of_neutral_cancellation bilinear projection neutral relative transverse
    leftNeutral rightNeutral transverseZero relativeBound).trans
    ((mul_le_mul_of_nonneg_left meanBound (by positivity : 0 ≤ 3 * ‖projection‖ * ‖bilinear‖ * ‖transverse‖)).trans_eq
      (by ring))

end EulerNonuniqueness.General
