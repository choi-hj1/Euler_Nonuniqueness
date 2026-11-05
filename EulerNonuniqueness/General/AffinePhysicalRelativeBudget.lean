import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EulerNonuniqueness.General

theorem affine_physical_relative_quadratic_budget
    (firstSize finalSize transverseSize transverseDifference neutralDifference
      defectDifference baseDifference shapeConstant baseConstant : ℝ)
    (firstNonnegative : 0 ≤ firstSize) (finalNonnegative : 0 ≤ finalSize)
    (sizeNonnegative : 0 ≤ transverseSize) (differenceNonnegative : 0 ≤ transverseDifference)
    (neutralNonnegative : 0 ≤ neutralDifference) (shapeNonnegative : 0 ≤ shapeConstant)
    (baseNonnegative : 0 ≤ baseConstant)
    (sizes : firstSize + finalSize ≤ shapeConstant * transverseSize)
    (defects : defectDifference ≤ shapeConstant *
      (transverseDifference + transverseSize * neutralDifference))
    (bases : baseDifference ≤ baseConstant * neutralDifference) :
    (firstSize + finalSize) * defectDifference + baseDifference * (firstSize + finalSize) ^ 2 ≤
      shapeConstant ^ 2 * (1 + baseConstant) *
        (transverseSize * transverseDifference + transverseSize ^ 2 * neutralDifference) := by
  have sizeSum : 0 ≤ firstSize + finalSize := add_nonneg firstNonnegative finalNonnegative
  have firstBound : (firstSize + finalSize) * defectDifference ≤
      (shapeConstant * transverseSize) *
        (shapeConstant * (transverseDifference + transverseSize * neutralDifference)) :=
    (mul_le_mul_of_nonneg_left defects sizeSum).trans
      (mul_le_mul_of_nonneg_right sizes (by positivity))
  have squareBound : (firstSize + finalSize) ^ 2 ≤ (shapeConstant * transverseSize) ^ 2 :=
    pow_le_pow_left₀ sizeSum sizes 2
  have finalBound : baseDifference * (firstSize + finalSize) ^ 2 ≤
      (baseConstant * neutralDifference) * (shapeConstant * transverseSize) ^ 2 :=
    (mul_le_mul_of_nonneg_right bases (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left squareBound (mul_nonneg baseNonnegative neutralNonnegative))
  have spare : 0 ≤ shapeConstant ^ 2 * baseConstant * transverseSize * transverseDifference := by positivity
  nlinarith [add_le_add firstBound finalBound]

end EulerNonuniqueness.General
