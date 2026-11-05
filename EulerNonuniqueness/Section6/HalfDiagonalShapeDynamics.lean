import EulerNonuniqueness.Section6.HalfDiagonalCanonicalProfile
import EulerNonuniqueness.Section6.UpperShapeBranch

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem pointShapeChart_eq_halfDiagonalShape_of_upper {positive negative : ℂ}
    (upper : 0 < (negative / positive).im) :
    pointShapeChart positive negative = halfDiagonalShape positive negative := by
  rw [pointShapeChart, pointShapeAngle_eq_twice_arg_of_upper upper]
  simp only [shapeChart, pointShapeRatio, halfDiagonalShape]
  rw [div_sub_one EulerNonuniqueness.Section2.rhombusRatio_pos.ne']
  rfl

theorem halfDiagonalShape_unforced_hasDerivAt
    {positive negative : ℝ → ℂ} {coefficient time : ℝ}
    (differencePositive : 0 < ‖positive time‖ ^ 2 - ‖negative time‖ ^ 2)
    (upper : 0 < (negative time / positive time).im)
    (small : |(halfDiagonalShape (positive time) (negative time)).1| +
      |(halfDiagonalShape (positive time) (negative time)).2| ≤ 1 / 4)
    (positiveDerivative : HasDerivAt positive (positivePointVelocity coefficient (positive time) (negative time)) time)
    (negativeDerivative : HasDerivAt negative (negativePointVelocity coefficient (positive time) (negative time)) time) :
    HasDerivAt (fun current => halfDiagonalShape (positive current) (negative current))
      (shapeChartVelocity (coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2))
        (halfDiagonalShape (positive time) (negative time))) time := by
  have positiveNorm : 0 < ‖positive time‖ := by nlinarith [norm_nonneg (positive time), sq_nonneg ‖negative time‖]
  have positiveNonzero : positive time ≠ 0 := norm_pos_iff.mp positiveNorm
  have negativeNonzero : negative time ≠ 0 := by
    intro zero
    simp only [zero, zero_div, Complex.zero_im, lt_irrefl] at upper
  have normOrder : ‖negative time‖ < ‖positive time‖ := by nlinarith [norm_nonneg (negative time)]
  have differenceNonzero : positive time - negative time ≠ 0 := by
    intro zero
    rw [sub_eq_zero.mp zero] at normOrder
    exact lt_irrefl _ normOrder
  have sumNonzero : positive time + negative time ≠ 0 := by
    intro zero
    have equal : negative time = -positive time := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using zero)
    rw [equal, norm_neg] at normOrder
    exact lt_irrefl _ normOrder
  have squareNonzero : star (positive time) ^ 2 - star (negative time) ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by simpa only [star_add] using star_ne_zero.mpr sumNonzero)
      (by simpa only [star_sub] using star_ne_zero.mpr differenceNonzero)
  have chartIdentity := pointShapeChart_eq_halfDiagonalShape_of_upper upper
  have coherentSmall : |(pointShapeChart (positive time) (negative time)).1| +
      |(pointShapeChart (positive time) (negative time)).2| ≤ 1 / 4 := by rwa [chartIdentity]
  have actual := pointShapeChart_forced_equation coefficient positiveNonzero negativeNonzero squareNonzero normOrder
    (pointShapeChart_leftHalfPlane_of_small positiveNonzero negativeNonzero coherentSmall)
    (positiveForcing := 0) (negativeForcing := 0) (by simpa using positiveDerivative) (by simpa using negativeDerivative)
  simp only [pointShapeForcing, zero_div, sub_self, Complex.zero_re, Complex.zero_im, mul_zero,
    zero_div, zero_add, add_zero, Prod.mk_zero_zero, chartIdentity] at actual
  apply actual.congr_of_eventuallyEq
  have quotientContinuous := negativeDerivative.continuousAt.div positiveDerivative.continuousAt positiveNonzero
  have eventuallyUpper := continuousAt_const.eventually_lt
    (Complex.continuous_im.continuousAt.comp quotientContinuous) upper
  exact eventuallyUpper.mono fun current currentUpper => (pointShapeChart_eq_halfDiagonalShape_of_upper currentUpper).symm

end EulerNonuniqueness.Section6
