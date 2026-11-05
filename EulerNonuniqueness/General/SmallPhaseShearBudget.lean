import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

theorem small_phase_shear_budget
    {frequency dilation difference reference defect constant radius tolerance : ℝ}
    (frequencyNonnegative : 0 ≤ frequency) (dilationNonnegative : 0 ≤ dilation)
    (differenceNonnegative : 0 ≤ difference) (referenceNonnegative : 0 ≤ reference)
    (defectNonnegative : 0 ≤ defect) (constantNonnegative : 0 ≤ constant)
    (radiusNonnegative : 0 ≤ radius) (radiusOne : radius ≤ 1)
    (dilationSmall : dilation ≤ radius) (differenceSmall : difference ≤ radius)
    (referenceSmall : reference ≤ radius) (defectSmall : defect ≤ radius)
    (budget : 100 * (constant + 1) * radius ≤ tolerance) :
    4 * frequency * dilation * (2 * dilation + 3 * defect) +
      2 * frequency * constant * ((difference + 2 * reference) * difference) +
      4 * frequency * dilation * (constant * reference ^ 2) ≤
        tolerance * frequency * (dilation + difference) := by
  have referenceSquare : reference ^ 2 ≤ radius := by
    have actual := mul_le_mul referenceSmall referenceSmall referenceNonnegative radiusNonnegative
    nlinarith [mul_nonneg radiusNonnegative (sub_nonneg.mpr radiusOne)]
  have first := mul_le_mul_of_nonneg_left
    (show 2 * dilation + 3 * defect ≤ 5 * radius by linarith) (by positivity : 0 ≤ 4 * frequency * dilation)
  have second := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (show difference + 2 * reference ≤ 3 * radius by linarith) differenceNonnegative)
    (by positivity : 0 ≤ 2 * frequency * constant)
  have third := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left referenceSquare constantNonnegative) (by positivity : 0 ≤ 4 * frequency * dilation)
  have dilationCoefficient : (20 + 4 * constant) * radius ≤ tolerance := by
    nlinarith [mul_nonneg constantNonnegative radiusNonnegative]
  have differenceCoefficient : 6 * constant * radius ≤ tolerance := by
    nlinarith [mul_nonneg constantNonnegative radiusNonnegative]
  have dilationBound := mul_le_mul_of_nonneg_right dilationCoefficient (mul_nonneg frequencyNonnegative dilationNonnegative)
  have differenceBound := mul_le_mul_of_nonneg_right differenceCoefficient (mul_nonneg frequencyNonnegative differenceNonnegative)
  nlinarith

end EulerNonuniqueness.General
