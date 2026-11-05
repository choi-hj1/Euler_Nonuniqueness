import EulerNonuniqueness.General.LocalFiberOperatorBounds

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target]

theorem norm_scaled_fiber_relative_quadratic_le
    (initialCoordinates finalCoordinates : Space →L[ℝ] Space)
    (first second : Space) (initial intermediate final : Target)
    {constant bound distance : ℝ}
    (constantNonnegative : 0 ≤ constant) (boundLarge : 1 ≤ bound) (distanceNonnegative : 0 ≤ distance)
    (initialNorm : ‖initialCoordinates‖ ≤ bound) (finalNorm : ‖finalCoordinates‖ ≤ bound)
    (coordinateDifference : ‖initialCoordinates - finalCoordinates‖ ≤ bound * distance)
    (incrementBound : ‖initial - intermediate‖ ≤ constant *
      (‖initialCoordinates first‖ + ‖initialCoordinates second‖) *
        ‖initialCoordinates first - initialCoordinates second‖)
    (parameterBound : ‖intermediate - final‖ ≤ constant *
      ((‖initialCoordinates second‖ + ‖finalCoordinates second‖) *
        ‖initialCoordinates second - finalCoordinates second‖ +
          (bound * distance) * ‖finalCoordinates second‖ ^ 2)) :
    ‖initial - final‖ ≤ 3 * constant * bound ^ 3 *
      ((‖first‖ + ‖second‖) * ‖first - second‖ + distance * ‖second‖ ^ 2) := by
  have boundNonnegative : 0 ≤ bound := le_trans (by norm_num) boundLarge
  have applyInitial (vector : Space) : ‖initialCoordinates vector‖ ≤ bound * ‖vector‖ :=
    (initialCoordinates.le_opNorm vector).trans (mul_le_mul_of_nonneg_right initialNorm (norm_nonneg _))
  have applyFinal (vector : Space) : ‖finalCoordinates vector‖ ≤ bound * ‖vector‖ :=
    (finalCoordinates.le_opNorm vector).trans (mul_le_mul_of_nonneg_right finalNorm (norm_nonneg _))
  have incrementDifference : ‖initialCoordinates first - initialCoordinates second‖ ≤ bound * ‖first - second‖ := by
    simpa only [map_sub] using applyInitial (first - second)
  have parameterDifference : ‖initialCoordinates second - finalCoordinates second‖ ≤ (bound * distance) * ‖second‖ := by
    exact ((initialCoordinates - finalCoordinates).le_opNorm second).trans
      (mul_le_mul_of_nonneg_right coordinateDifference (norm_nonneg _))
  have firstBound : ‖initial - intermediate‖ ≤
      constant * (bound * ‖first‖ + bound * ‖second‖) * (bound * ‖first - second‖) := by
    apply incrementBound.trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (add_le_add (applyInitial first) (applyInitial second)) constantNonnegative)
      incrementDifference (norm_nonneg _) (by positivity)
  have secondBound : ‖intermediate - final‖ ≤ constant *
      ((bound * ‖second‖ + bound * ‖second‖) * ((bound * distance) * ‖second‖) +
        (bound * distance) * (bound * ‖second‖) ^ 2) := by
    apply parameterBound.trans
    apply mul_le_mul_of_nonneg_left _ constantNonnegative
    apply add_le_add
    · exact mul_le_mul (add_le_add (applyInitial second) (applyFinal second)) parameterDifference
        (norm_nonneg _) (by positivity)
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (applyFinal second) 2) (by positivity)
  have squareLarge : bound ^ 2 ≤ bound ^ 3 := by nlinarith [sq_nonneg bound, mul_nonneg (sq_nonneg bound) (sub_nonneg.mpr boundLarge)]
  have firstFactor : constant * bound ^ 2 ≤ 3 * constant * bound ^ 3 := by nlinarith
  have secondFactor : constant * (2 * bound ^ 2 + bound ^ 3) ≤ 3 * constant * bound ^ 3 := by nlinarith
  apply (norm_sub_le_norm_sub_add_norm_sub initial intermediate final).trans
    ((add_le_add firstBound secondBound).trans ?_)
  calc
    _ = (constant * bound ^ 2) * ((‖first‖ + ‖second‖) * ‖first - second‖) +
        (constant * (2 * bound ^ 2 + bound ^ 3)) * (distance * ‖second‖ ^ 2) := by ring
    _ ≤ (3 * constant * bound ^ 3) * ((‖first‖ + ‖second‖) * ‖first - second‖) +
        (3 * constant * bound ^ 3) * (distance * ‖second‖ ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_right firstFactor (by positivity))
        (mul_le_mul_of_nonneg_right secondFactor (by positivity))
    _ = _ := by ring

end

end EulerNonuniqueness.General
