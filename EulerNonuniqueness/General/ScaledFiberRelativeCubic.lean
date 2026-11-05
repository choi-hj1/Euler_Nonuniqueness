import Mathlib

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_scaled_fiber_relative_cubic_le
    (first second : Space →L[ℝ] Space) (initial final errorInitial errorFinal : Space)
    {constant bound parameterDistance baseDistance : ℝ}
    (constantNonnegative : 0 ≤ constant) (boundLarge : 1 ≤ bound)
    (parameterNonnegative : 0 ≤ parameterDistance)
    (baseNonnegative : 0 ≤ baseDistance)
    (firstBound : ‖first‖ ≤ bound) (secondBound : ‖second‖ ≤ bound)
    (differenceBound : ‖first - second‖ ≤ bound * parameterDistance)
    (baseBound : baseDistance ≤ bound * parameterDistance)
    (errorBound : ‖errorInitial - errorFinal‖ ≤ constant *
      ((‖first initial‖ + ‖second final‖) ^ 2 * ‖first initial - second final‖ +
        baseDistance * ‖second final‖ ^ 3)) :
    ‖errorInitial - errorFinal‖ ≤ 2 * constant * bound ^ 4 *
      ((‖initial‖ + ‖final‖) ^ 2 * ‖initial - final‖ +
        (‖initial‖ + ‖final‖) ^ 3 * parameterDistance) := by
  have boundNonnegative : 0 ≤ bound := le_trans (by norm_num) boundLarge
  have imageInitial : ‖first initial‖ ≤ bound * ‖initial‖ :=
    (first.le_opNorm _).trans (mul_le_mul_of_nonneg_right firstBound (norm_nonneg _))
  have imageFinal : ‖second final‖ ≤ bound * ‖final‖ :=
    (second.le_opNorm _).trans (mul_le_mul_of_nonneg_right secondBound (norm_nonneg _))
  have identity : first initial - second final = first (initial - final) + (first - second) final := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
    abel
  have imageDifference : ‖first initial - second final‖ ≤
      bound * ‖initial - final‖ + bound * parameterDistance * ‖final‖ := by
    rw [identity]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (first.le_opNorm _).trans (mul_le_mul_of_nonneg_right firstBound (norm_nonneg _))
    · exact ((first - second).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right differenceBound (norm_nonneg _))
  have finalNorm : ‖final‖ ≤ ‖initial‖ + ‖final‖ := le_add_of_nonneg_left (norm_nonneg initial)
  have imageSum : ‖first initial‖ + ‖second final‖ ≤ bound * (‖initial‖ + ‖final‖) := by
    linarith
  have imageFinalSum : ‖second final‖ ≤ bound * (‖initial‖ + ‖final‖) :=
    imageFinal.trans (mul_le_mul_of_nonneg_left finalNorm boundNonnegative)
  have differenceSum : ‖first initial - second final‖ ≤
      bound * ‖initial - final‖ + bound * parameterDistance * (‖initial‖ + ‖final‖) := by
    exact imageDifference.trans (add_le_add_left
      (mul_le_mul_of_nonneg_left finalNorm (mul_nonneg boundNonnegative parameterNonnegative)) _)
  have power : bound ^ 3 ≤ bound ^ 4 := by
    have positive := pow_nonneg boundNonnegative 3
    nlinarith
  apply errorBound.trans
  calc
    _ ≤ constant * ((bound * (‖initial‖ + ‖final‖)) ^ 2 *
          (bound * ‖initial - final‖ + bound * parameterDistance * (‖initial‖ + ‖final‖)) +
        (bound * parameterDistance) * (bound * (‖initial‖ + ‖final‖)) ^ 3) := by
      gcongr
    _ = constant * bound ^ 3 * ((‖initial‖ + ‖final‖) ^ 2 * ‖initial - final‖) +
        constant * bound ^ 3 * ((‖initial‖ + ‖final‖) ^ 3 * parameterDistance) +
        constant * bound ^ 4 * ((‖initial‖ + ‖final‖) ^ 3 * parameterDistance) := by ring
    _ ≤ constant * bound ^ 4 * ((‖initial‖ + ‖final‖) ^ 2 * ‖initial - final‖) +
        constant * bound ^ 4 * ((‖initial‖ + ‖final‖) ^ 3 * parameterDistance) +
        constant * bound ^ 4 * ((‖initial‖ + ‖final‖) ^ 3 * parameterDistance) := by
      gcongr
    _ ≤ _ := by
      have nonnegative : 0 ≤ constant * bound ^ 4 *
          ((‖initial‖ + ‖final‖) ^ 2 * ‖initial - final‖) := by positivity
      nlinarith

end EulerNonuniqueness.General
