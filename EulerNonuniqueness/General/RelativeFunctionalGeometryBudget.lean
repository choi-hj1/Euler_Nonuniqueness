import Mathlib

namespace EulerNonuniqueness.General

theorem relative_functional_geometry_budget
    {defectDifference baseDifference finalDefect transverseDifference transverseSum neutralDifference
      shapeConstant baseConstant : ℝ}
    (transverseNonnegative : 0 ≤ transverseDifference) (sumNonnegative : 0 ≤ transverseSum)
    (neutralNonnegative : 0 ≤ neutralDifference) (shapeNonnegative : 0 ≤ shapeConstant)
    (baseNonnegative : 0 ≤ baseConstant) (baseDifferenceNonnegative : 0 ≤ baseDifference)
    (defectNonnegative : 0 ≤ finalDefect)
    (relative : defectDifference ≤ shapeConstant * (transverseDifference + transverseSum * neutralDifference))
    (base : baseDifference ≤ baseConstant * neutralDifference)
    (defect : finalDefect ≤ shapeConstant * transverseSum) :
    defectDifference + baseDifference * finalDefect ≤
      shapeConstant * (1 + baseConstant) * (transverseDifference + transverseSum * neutralDifference) := by
  have product := mul_le_mul base defect defectNonnegative (mul_nonneg baseNonnegative neutralNonnegative)
  have extra : 0 ≤ shapeConstant * baseConstant * transverseDifference := by positivity
  nlinarith only [relative, product, extra]

end EulerNonuniqueness.General
