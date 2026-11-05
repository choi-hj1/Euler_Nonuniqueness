import Mathlib

namespace EulerNonuniqueness.General

theorem affine_inverse_pullback_relative_budget
    (initial final difference neutral firstCoefficient finalCoefficient coefficientDifference
      inverseConstant stateConstant relativeConstant absoluteConstant : ℝ)
    (initialNonnegative : 0 ≤ initial) (finalNonnegative : 0 ≤ final)
    (differenceNonnegative : 0 ≤ difference) (neutralNonnegative : 0 ≤ neutral)
    (firstCoefficientNonnegative : 0 ≤ firstCoefficient)
    (finalCoefficientNonnegative : 0 ≤ finalCoefficient)
    (coefficientDifferenceNonnegative : 0 ≤ coefficientDifference)
    (inverseNonnegative : 0 ≤ inverseConstant) (stateNonnegative : 0 ≤ stateConstant)
    (relativeNonnegative : 0 ≤ relativeConstant) (absoluteNonnegative : 0 ≤ absoluteConstant)
    (small : initial + final ≤ 1) :
    inverseConstant * (relativeConstant *
      (firstCoefficient * ((initial + final) * difference + (initial + final) ^ 2 * neutral) +
        coefficientDifference * final ^ 2)) +
      (inverseConstant * (stateConstant * (difference + neutral))) *
        (absoluteConstant * finalCoefficient * final ^ 2) ≤
    (inverseConstant * (relativeConstant + stateConstant * absoluteConstant)) *
      ((firstCoefficient + finalCoefficient) *
        ((initial + final) * difference + (initial + final) ^ 2 * neutral) +
        coefficientDifference * final ^ 2) := by
  have finalLe : final ≤ initial + final := le_add_of_nonneg_left initialNonnegative
  have finalOne : final ≤ 1 := finalLe.trans small
  have squareFinal : final ^ 2 ≤ final := by nlinarith
  have squareLe : final ^ 2 ≤ (initial + final) ^ 2 :=
    pow_le_pow_left₀ finalNonnegative finalLe 2
  have budget : final ^ 2 * (difference + neutral) ≤
      (initial + final) * difference + (initial + final) ^ 2 * neutral := by
    have first := mul_le_mul_of_nonneg_right (squareFinal.trans finalLe) differenceNonnegative
    have second := mul_le_mul_of_nonneg_right squareLe neutralNonnegative
    nlinarith
  have weighted := mul_le_mul_of_nonneg_left budget
    (show 0 ≤ inverseConstant * stateConstant * absoluteConstant * finalCoefficient by positivity)
  have spareFirst : 0 ≤ inverseConstant * relativeConstant * finalCoefficient *
      ((initial + final) * difference + (initial + final) ^ 2 * neutral) := by positivity
  have spareSecond : 0 ≤ inverseConstant * stateConstant * absoluteConstant * firstCoefficient *
      ((initial + final) * difference + (initial + final) ^ 2 * neutral) := by positivity
  have spareThird : 0 ≤ inverseConstant * stateConstant * absoluteConstant * coefficientDifference * final ^ 2 := by positivity
  nlinarith

end EulerNonuniqueness.General
