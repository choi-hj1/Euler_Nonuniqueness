import EulerNonuniqueness.General.AffineResidualRelativeRemainder

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_linear_quadratic_constraint_difference_le
    (first second : Space →L[ℝ] Space) (initial final : Space)
    {linearConstant quadraticConstant amplitude size increment baseDifference finalSize : ℝ}
    (linearNonnegative : 0 ≤ linearConstant) (quadraticNonnegative : 0 ≤ quadraticConstant)
    (amplitudeNonnegative : 0 ≤ amplitude) (sizeNonnegative : 0 ≤ size)
    (incrementNonnegative : 0 ≤ increment) (baseNonnegative : 0 ≤ baseDifference)
    (finalNonnegative : 0 ≤ finalSize) (finalBound : finalSize ≤ size)
    (firstBound : ‖first‖ ≤ linearConstant * amplitude)
    (differenceBound : ‖first - second‖ ≤ linearConstant * amplitude * baseDifference)
    (vectorDifference : ‖initial - final‖ ≤ quadraticConstant *
      (size * increment + baseDifference * finalSize ^ 2))
    (vectorBound : ‖final‖ ≤ quadraticConstant * finalSize ^ 2) :
    ‖first initial - second final‖ ≤ 2 * linearConstant * quadraticConstant * amplitude *
      (size * increment + baseDifference * size ^ 2) := by
  have squareBound := pow_le_pow_left₀ finalNonnegative finalBound 2
  have budgetBound : size * increment + baseDifference * finalSize ^ 2 ≤
      size * increment + baseDifference * size ^ 2 :=
    add_le_add_left (mul_le_mul_of_nonneg_left squareBound baseNonnegative) _
  have finalCost : baseDifference * finalSize ^ 2 ≤ size * increment + baseDifference * size ^ 2 :=
    (mul_le_mul_of_nonneg_left squareBound baseNonnegative).trans (le_add_of_nonneg_left (by positivity))
  have estimate := norm_operator_apply_difference_le first second initial final
  apply estimate.trans
  calc
    _ ≤ (linearConstant * amplitude) *
        (quadraticConstant * (size * increment + baseDifference * finalSize ^ 2)) +
        (linearConstant * amplitude * baseDifference) * (quadraticConstant * finalSize ^ 2) := by gcongr
    _ = linearConstant * quadraticConstant * amplitude *
        (size * increment + baseDifference * finalSize ^ 2) +
        linearConstant * quadraticConstant * amplitude * (baseDifference * finalSize ^ 2) := by ring
    _ ≤ linearConstant * quadraticConstant * amplitude * (size * increment + baseDifference * size ^ 2) +
        linearConstant * quadraticConstant * amplitude * (size * increment + baseDifference * size ^ 2) := by gcongr
    _ = _ := by ring

end EulerNonuniqueness.General
