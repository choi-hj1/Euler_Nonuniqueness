import EulerNonuniqueness.Section6.ReferenceShapeChartDomain
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem unwrappedShapeArgument_square_of_im_pos {point : ℂ} (upper : 0 < point.im) :
    unwrappedShapeArgument (point ^ 2) = 2 * Complex.arg point := by
  have nonzero : point ≠ 0 := by
    intro zero
    rw [zero, Complex.zero_im] at upper
    exact lt_irrefl 0 upper
  have argumentNonnegative : 0 ≤ Complex.arg point := Complex.arg_nonneg_iff.mpr upper.le
  have argumentBelowPi : Complex.arg point < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr upper.ne')
  by_cases lower : Complex.arg point ≤ Real.pi / 2
  · have squareArgument : Complex.arg (point ^ 2) = Complex.arg point + Complex.arg point := by
      rw [pow_two]
      exact Complex.arg_mul nonzero nonzero ⟨by linarith [Real.pi_pos], by linarith⟩
    rw [unwrappedShapeArgument, squareArgument, if_neg (by linarith : ¬ Complex.arg point + Complex.arg point < 0)]
    ring
  · have negativeArgument := Complex.arg_neg_eq_arg_sub_pi_of_im_pos upper
    have squareArgument : Complex.arg ((-point) ^ 2) = Complex.arg (-point) + Complex.arg (-point) := by
      rw [pow_two]
      apply Complex.arg_mul (neg_ne_zero.mpr nonzero) (neg_ne_zero.mpr nonzero)
      rw [negativeArgument]
      constructor <;> linarith [Real.pi_pos]
    have sameSquare : (-point) ^ 2 = point ^ 2 := by ring
    rw [sameSquare, negativeArgument] at squareArgument
    rw [unwrappedShapeArgument, squareArgument, if_pos (by linarith :
      Complex.arg point - Real.pi + (Complex.arg point - Real.pi) < 0)]
    ring

theorem upperHalfPlane_of_initial_and_square_left {field : ℝ → ℂ} {horizon : ℝ}
    (continuous : ContinuousOn field (Icc 0 horizon)) (initial : 0 < (field 0).im)
    (left : ∀ time ∈ Icc 0 horizon, ((field time) ^ 2).re < 0) :
    ∀ time ∈ Icc 0 horizon, 0 < (field time).im := by
  have nonzero (time : ℝ) (member : time ∈ Icc 0 horizon) : (field time).im ≠ 0 := by
    intro zero
    have negative := left time member
    simp only [pow_two, Complex.mul_re, zero, mul_zero, sub_zero] at negative
    nlinarith [sq_nonneg (field time).re]
  intro time member
  by_contra notPositive
  have finalNonpositive : (field time).im ≤ 0 := le_of_not_gt notPositive
  have subset : Icc (0 : ℝ) time ⊆ Icc 0 horizon := Icc_subset_Icc le_rfl member.2
  have realContinuous : ContinuousOn (fun current => (field current).im) (Icc 0 time) :=
    Complex.continuous_im.comp_continuousOn (continuous.mono subset)
  obtain ⟨middle, middleInside, zero⟩ := intermediate_value_Icc' member.1 realContinuous
    (show (0 : ℝ) ∈ Icc (field time).im (field 0).im from ⟨finalNonpositive, initial.le⟩)
  exact nonzero middle (subset middleInside) zero

theorem pointShapeAngle_eq_twice_arg_of_upper {positive negative : ℂ}
    (upper : 0 < (negative / positive).im) :
    pointShapeAngle positive negative = 2 * Complex.arg (negative / positive) :=
  unwrappedShapeArgument_square_of_im_pos upper

end EulerNonuniqueness.Section6
