import EulerNonuniqueness.General.RelativeMeanCubicBudget

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space]

theorem norm_relative_cubic_after_mean_absorption
    (initialError finalError initial final first second firstTransverse finalTransverse : Space)
    {constant meanCoefficient neutralDistance : ℝ}
    (constantNonnegative : 0 ≤ constant) (meanNonnegative : 0 ≤ meanCoefficient)
    (neutralNonnegative : 0 ≤ neutralDistance)
    (sizeSmall : ‖firstTransverse‖ + ‖finalTransverse‖ ≤ 1)
    (firstBound : ‖first‖ ≤ 2 * ‖firstTransverse‖)
    (finalBound : ‖second‖ ≤ 2 * ‖finalTransverse‖)
    (relativeDifference : ‖first - second‖ ≤ ‖firstTransverse - finalTransverse‖ + meanCoefficient *
      ((‖firstTransverse‖ + ‖finalTransverse‖) * ‖firstTransverse - finalTransverse‖ +
        neutralDistance * ‖finalTransverse‖ ^ 2))
    (stateDifference : ‖initial - final‖ ≤ neutralDistance + ‖first - second‖)
    (rawBound : ‖initialError - finalError‖ ≤ constant *
      ((‖first‖ + ‖second‖) ^ 2 * ‖first - second‖ +
        (‖first‖ + ‖second‖) ^ 3 * ‖initial - final‖)) :
    ‖initialError - finalError‖ ≤ 20 * constant * (meanCoefficient + 1) *
      ((‖firstTransverse‖ + ‖finalTransverse‖) ^ 2 * ‖firstTransverse - finalTransverse‖ +
        (‖firstTransverse‖ + ‖finalTransverse‖) ^ 3 * neutralDistance) := by
  have normSum : ‖first‖ + ‖second‖ ≤ 2 * (‖firstTransverse‖ + ‖finalTransverse‖) := by linarith
  have squareBound := pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) normSum 2
  have cubeBound := pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) normSum 3
  have fullDifference := stateDifference.trans (add_le_add_left relativeDifference neutralDistance)
  apply relative_mean_cubic_budget constantNonnegative meanNonnegative (by positivity) sizeSmall
    (norm_nonneg _) (le_add_of_nonneg_left (norm_nonneg _)) (norm_nonneg _) neutralNonnegative
  apply rawBound.trans
  have squareEstimate := mul_le_mul squareBound relativeDifference (norm_nonneg _) (by positivity)
  have cubeEstimate := mul_le_mul cubeBound fullDifference (norm_nonneg _) (by positivity)
  have total := mul_le_mul_of_nonneg_left (add_le_add squareEstimate cubeEstimate) constantNonnegative
  convert total using 1 <;> ring

end EulerNonuniqueness.General
