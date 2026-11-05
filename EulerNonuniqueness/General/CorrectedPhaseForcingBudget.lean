import Mathlib

namespace EulerNonuniqueness.General

theorem corrected_phase_forcing_relative_budget
    {output logarithm rawDifference pointDifference total pointValue moment positions rawCoordinate error source
      coefficient derivative transport tolerance : ℝ}
    (momentNonnegative : 0 ≤ moment) (positionsNonnegative : 0 ≤ positions) (coordinateNonnegative : 0 ≤ rawCoordinate)
    (errorNonnegative : 0 ≤ error) (sourceNonnegative : 0 ≤ source)
    (coefficientNonnegative : 0 ≤ coefficient) (derivativeNonnegative : 0 ≤ derivative) (transportNonnegative : 0 ≤ transport)
    (actual : output ≤ logarithm + coefficient * pointDifference + derivative * rawCoordinate * pointValue)
    (logarithmBound : logarithm ≤ 2 * rawDifference + 4 * total * positions)
    (rawBound : rawDifference ≤ transport * (moment + positions) + error + 3 * source)
    (pointBound : pointDifference ≤ transport * (moment + positions) + 30 * error + 90 * source)
    (totalBound : total ≤ transport) (valueBound : pointValue ≤ transport)
    (budget : (6 + coefficient + derivative) * transport ≤ tolerance) :
    output ≤ tolerance * (moment + positions + rawCoordinate) + (8 + 120 * coefficient) * (error + source) := by
  have enlarged := actual.trans (add_le_add
    (add_le_add logarithmBound (mul_le_mul_of_nonneg_left pointBound coefficientNonnegative))
    (mul_le_mul_of_nonneg_left valueBound (mul_nonneg derivativeNonnegative coordinateNonnegative)))
  have totalTerm := mul_le_mul_of_nonneg_right totalBound (show 0 ≤ 4 * positions by positivity)
  have rawTerm := mul_le_mul_of_nonneg_left rawBound (by norm_num : (0 : ℝ) ≤ 2)
  have firstBudget : (2 + coefficient) * transport ≤ tolerance := by
    nlinarith only [budget, mul_nonneg (show 0 ≤ 4 + derivative by positivity) transportNonnegative]
  have secondBudget : (6 + coefficient) * transport ≤ tolerance := by
    nlinarith only [budget, mul_nonneg derivativeNonnegative transportNonnegative]
  have thirdBudget : derivative * transport ≤ tolerance := by
    nlinarith only [budget, mul_nonneg (show 0 ≤ 6 + coefficient by positivity) transportNonnegative]
  have first := mul_le_mul_of_nonneg_right firstBudget momentNonnegative
  have second := mul_le_mul_of_nonneg_right secondBudget positionsNonnegative
  have third := mul_le_mul_of_nonneg_right thirdBudget coordinateNonnegative
  have sourceFirst : (2 + 30 * coefficient) * error ≤ (8 + 120 * coefficient) * error := by
    nlinarith [mul_nonneg coefficientNonnegative errorNonnegative]
  have sourceSecond : (6 + 90 * coefficient) * source ≤ (8 + 120 * coefficient) * source := by
    nlinarith [mul_nonneg coefficientNonnegative sourceNonnegative]
  nlinarith only [enlarged, rawTerm, totalTerm, first, second, third, sourceFirst, sourceSecond]

end EulerNonuniqueness.General
