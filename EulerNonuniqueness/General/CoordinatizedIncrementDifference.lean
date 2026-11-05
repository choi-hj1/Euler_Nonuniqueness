import EulerNonuniqueness.General.RelativeLinearIncrement

noncomputable section

namespace EulerNonuniqueness.General

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem coordinatized_increment_difference_norm_le
    (function : Domain → Target) (first second initial final : Domain)
    (firstCoordinates secondCoordinates : Domain →L[ℝ] Domain)
    {constant coordinateBound : ℝ} (constantNonnegative : 0 ≤ constant)
    (coordinateNonnegative : 0 ≤ coordinateBound)
    (firstBound : ‖firstCoordinates‖ ≤ coordinateBound)
    (secondBound : ‖secondCoordinates‖ ≤ coordinateBound)
    (coordinateDifference : ‖firstCoordinates - secondCoordinates‖ ≤ coordinateBound * ‖first - second‖)
    (raw : ‖(function (first + firstCoordinates initial) - function first) -
      (function (second + secondCoordinates final) - function second)‖ ≤
      constant * (‖firstCoordinates initial - secondCoordinates final‖ +
        ‖first - second‖ * ‖secondCoordinates final‖)) :
    ‖(function (first + firstCoordinates initial) - function first) -
      (function (second + secondCoordinates final) - function second)‖ ≤
      (2 * constant * coordinateBound) * (‖initial - final‖ + ‖first - second‖ * ‖final‖) := by
  have applied : ‖secondCoordinates final‖ ≤ coordinateBound * ‖final‖ :=
    (secondCoordinates.le_opNorm final).trans (mul_le_mul_of_nonneg_right secondBound (norm_nonneg _))
  have identity : firstCoordinates initial - secondCoordinates final =
      firstCoordinates (initial - final) + (firstCoordinates - secondCoordinates) final := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  have differenceBound : ‖firstCoordinates initial - secondCoordinates final‖ ≤
      coordinateBound * ‖initial - final‖ + coordinateBound * ‖first - second‖ * ‖final‖ := by
    rw [identity]
    apply (norm_add_le _ _).trans
    exact add_le_add
      ((firstCoordinates.le_opNorm _).trans (mul_le_mul_of_nonneg_right firstBound (norm_nonneg _)))
      (((firstCoordinates - secondCoordinates).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right coordinateDifference (norm_nonneg _)))
  apply raw.trans
  calc
    _ ≤ constant * (coordinateBound * ‖initial - final‖ +
        coordinateBound * ‖first - second‖ * ‖final‖ + ‖first - second‖ * (coordinateBound * ‖final‖)) := by
      gcongr
    _ ≤ _ := by
      have extra : 0 ≤ constant * coordinateBound * ‖initial - final‖ := by positivity
      nlinarith only [extra]

end EulerNonuniqueness.General
