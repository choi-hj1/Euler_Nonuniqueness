import Mathlib

namespace EulerNonuniqueness.General

theorem relative_mean_cubic_budget
    {constant meanCoefficient size finalSize difference parameterDifference remainder : ℝ}
    (constantNonnegative : 0 ≤ constant) (meanNonnegative : 0 ≤ meanCoefficient)
    (sizeNonnegative : 0 ≤ size) (sizeSmall : size ≤ 1)
    (finalNonnegative : 0 ≤ finalSize) (finalBound : finalSize ≤ size)
    (differenceNonnegative : 0 ≤ difference) (parameterNonnegative : 0 ≤ parameterDifference)
    (bound : remainder ≤ constant *
      (4 * size ^ 2 * (difference + meanCoefficient * (size * difference + parameterDifference * finalSize ^ 2)) +
        8 * size ^ 3 * (parameterDifference + difference +
          meanCoefficient * (size * difference + parameterDifference * finalSize ^ 2)))) :
    remainder ≤ 20 * constant * (meanCoefficient + 1) *
      (size ^ 2 * difference + size ^ 3 * parameterDifference) := by
  have squareBound : finalSize ^ 2 ≤ size ^ 2 := pow_le_pow_left₀ finalNonnegative finalBound 2
  have cubeSquare : size ^ 3 ≤ size ^ 2 := by nlinarith [mul_nonneg (sq_nonneg size) (sub_nonneg.mpr sizeSmall)]
  have fourthCube : size ^ 4 ≤ size ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg sizeNonnegative 3) (sub_nonneg.mpr sizeSmall)]
  have sumBound : 4 * size ^ 2 + 8 * size ^ 3 ≤ 12 * size ^ 2 := by nlinarith
  have meanBudget : difference + meanCoefficient * (size * difference + parameterDifference * finalSize ^ 2) ≤
      (meanCoefficient + 1) * difference + meanCoefficient * parameterDifference * size ^ 2 := by
    have first := mul_le_mul_of_nonneg_right sizeSmall differenceNonnegative
    have second := mul_le_mul_of_nonneg_left squareBound parameterNonnegative
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add first second) meanNonnegative]
  apply bound.trans
  calc
    _ = constant * ((4 * size ^ 2 + 8 * size ^ 3) *
        (difference + meanCoefficient * (size * difference + parameterDifference * finalSize ^ 2)) +
          8 * size ^ 3 * parameterDifference) := by ring
    _ ≤ constant * ((12 * size ^ 2) *
        ((meanCoefficient + 1) * difference + meanCoefficient * parameterDifference * size ^ 2) +
          8 * size ^ 3 * parameterDifference) :=
      mul_le_mul_of_nonneg_left (add_le_add_right
        (mul_le_mul sumBound meanBudget (by positivity) (by positivity)) _) constantNonnegative
    _ = constant * (12 * (meanCoefficient + 1) * size ^ 2 * difference +
        12 * meanCoefficient * parameterDifference * size ^ 4 + 8 * size ^ 3 * parameterDifference) := by ring
    _ ≤ constant * (12 * (meanCoefficient + 1) * size ^ 2 * difference +
        12 * meanCoefficient * parameterDifference * size ^ 3 + 8 * size ^ 3 * parameterDifference) :=
      mul_le_mul_of_nonneg_left (add_le_add_right (add_le_add_left
        (mul_le_mul_of_nonneg_left fourthCube (by positivity)) _) _) constantNonnegative
    _ ≤ _ := by
      have first := mul_nonneg (by positivity : 0 ≤ constant * (meanCoefficient + 1))
        (mul_nonneg (sq_nonneg size) differenceNonnegative)
      have second := mul_nonneg (by positivity : 0 ≤ constant * (meanCoefficient + 1))
        (mul_nonneg (pow_nonneg sizeNonnegative 3) parameterNonnegative)
      nlinarith

end EulerNonuniqueness.General
