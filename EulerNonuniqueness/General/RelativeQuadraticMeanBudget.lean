import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem relative_quadratic_mean_cubic_budget
    {firstSize secondSize transverseDifference neutralDifference firstMean secondMean meanDifference
      meanConstant bilinearConstant circleNorm remainder : ℝ}
    (firstNonnegative : 0 ≤ firstSize) (secondNonnegative : 0 ≤ secondSize)
    (transverseNonnegative : 0 ≤ transverseDifference) (neutralNonnegative : 0 ≤ neutralDifference)
    (firstMeanNonnegative : 0 ≤ firstMean) (secondMeanNonnegative : 0 ≤ secondMean)
    (meanDifferenceNonnegative : 0 ≤ meanDifference) (meanConstantNonnegative : 0 ≤ meanConstant)
    (bilinearNonnegative : 0 ≤ bilinearConstant) (circleNonnegative : 0 ≤ circleNorm)
    (sizeSmall : firstSize + secondSize ≤ 1)
    (firstMeanBound : firstMean ≤ meanConstant * firstSize ^ 2)
    (secondMeanBound : secondMean ≤ meanConstant * secondSize ^ 2)
    (meanDifferenceBound : meanDifference ≤ meanConstant *
      ((firstSize + secondSize) * transverseDifference + neutralDifference * secondSize ^ 2))
    (remainderBound : remainder ≤
      meanDifference * (2 * bilinearConstant * circleNorm * firstSize) +
      secondMean * (2 * bilinearConstant * circleNorm * transverseDifference +
        2 * bilinearConstant * neutralDifference * circleNorm * secondSize) +
      (firstMean + secondMean) * meanDifference * (bilinearConstant * circleNorm ^ 2) +
      secondMean ^ 2 * (bilinearConstant * neutralDifference * circleNorm ^ 2)) :
    remainder ≤ (4 * meanConstant * bilinearConstant * circleNorm +
      2 * meanConstant ^ 2 * bilinearConstant * circleNorm ^ 2) *
      ((firstSize + secondSize) ^ 2 * transverseDifference +
        (firstSize + secondSize) ^ 3 * neutralDifference) := by
  let total := firstSize + secondSize
  let budget := total ^ 2 * transverseDifference + total ^ 3 * neutralDifference
  have totalNonnegative : 0 ≤ total := add_nonneg firstNonnegative secondNonnegative
  have firstLe : firstSize ≤ total := le_add_of_nonneg_right secondNonnegative
  have secondLe : secondSize ≤ total := le_add_of_nonneg_left firstNonnegative
  have totalSmall : total ≤ 1 := sizeSmall
  have squareSum : firstSize ^ 2 + secondSize ^ 2 ≤ total ^ 2 := by
    dsimp only [total]
    nlinarith [mul_nonneg firstNonnegative secondNonnegative]
  have secondSquare := pow_le_pow_left₀ secondNonnegative secondLe 2
  have secondCube := pow_le_pow_left₀ secondNonnegative secondLe 3
  have totalCube : total ^ 3 ≤ total ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg total) (sub_nonneg.mpr totalSmall)]
  have totalFourth : total ^ 4 ≤ total ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg totalNonnegative 3) (sub_nonneg.mpr totalSmall)]
  have firstProduct : meanDifference * firstSize ≤ meanConstant * budget := by
    calc
      _ ≤ (meanConstant * (total * transverseDifference + neutralDifference * secondSize ^ 2)) * total := by
        gcongr
      _ ≤ (meanConstant * (total * transverseDifference + neutralDifference * total ^ 2)) * total := by
        gcongr
      _ = meanConstant * budget := by dsimp only [budget]; ring
  have secondProduct : secondMean * transverseDifference + secondMean * neutralDifference * secondSize ≤
      meanConstant * budget := by
    calc
      _ ≤ meanConstant * secondSize ^ 2 * transverseDifference +
          (meanConstant * secondSize ^ 2) * neutralDifference * secondSize := by gcongr
      _ = meanConstant * (secondSize ^ 2 * transverseDifference + secondSize ^ 3 * neutralDifference) := by ring
      _ ≤ meanConstant * budget := by dsimp only [budget]; gcongr
  have meanSum : firstMean + secondMean ≤ meanConstant * total ^ 2 :=
    (add_le_add firstMeanBound secondMeanBound).trans
      (by nlinarith [mul_le_mul_of_nonneg_left squareSum meanConstantNonnegative])
  have mixedProduct : (firstMean + secondMean) * meanDifference ≤ meanConstant ^ 2 * budget := by
    calc
      _ ≤ (meanConstant * total ^ 2) *
          (meanConstant * (total * transverseDifference + neutralDifference * secondSize ^ 2)) := by gcongr
      _ ≤ (meanConstant * total ^ 2) *
          (meanConstant * (total * transverseDifference + neutralDifference * total ^ 2)) := by gcongr
      _ = meanConstant ^ 2 * (total ^ 3 * transverseDifference + total ^ 4 * neutralDifference) := by ring
      _ ≤ meanConstant ^ 2 * budget := by dsimp only [budget]; gcongr
  have secondMeanSquare := pow_le_pow_left₀ secondMeanNonnegative secondMeanBound 2
  have fourthProduct : secondMean ^ 2 * neutralDifference ≤ meanConstant ^ 2 * budget := by
    calc
      _ ≤ (meanConstant * secondSize ^ 2) ^ 2 * neutralDifference := by gcongr
      _ ≤ (meanConstant * total ^ 2) ^ 2 * neutralDifference := by gcongr
      _ = meanConstant ^ 2 * (total ^ 4 * neutralDifference) := by ring
      _ ≤ meanConstant ^ 2 * (total ^ 3 * neutralDifference) := by gcongr
      _ ≤ meanConstant ^ 2 * budget := by
        dsimp only [budget]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (sq_nonneg _)
  have firstScaled := mul_le_mul_of_nonneg_left firstProduct
    (show 0 ≤ 2 * bilinearConstant * circleNorm by positivity)
  have secondScaled := mul_le_mul_of_nonneg_left secondProduct
    (show 0 ≤ 2 * bilinearConstant * circleNorm by positivity)
  have mixedScaled := mul_le_mul_of_nonneg_left mixedProduct
    (show 0 ≤ bilinearConstant * circleNorm ^ 2 by positivity)
  have fourthScaled := mul_le_mul_of_nonneg_left fourthProduct
    (show 0 ≤ bilinearConstant * circleNorm ^ 2 by positivity)
  have totalBound := add_le_add (add_le_add (add_le_add firstScaled secondScaled) mixedScaled) fourthScaled
  apply remainderBound.trans
  convert totalBound using 1 <;> dsimp only [total, budget] <;> ring

end EulerNonuniqueness.General
