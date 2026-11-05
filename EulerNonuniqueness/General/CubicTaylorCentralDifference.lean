import EulerNonuniqueness.General.BilinearPolarizationBound

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

def cubicTaylorError (function : Domain → Range) (linear : Domain → Domain →L[ℝ] Range)
    (quadratic : Domain → Domain →L[ℝ] Domain →L[ℝ] Range) (base increment : Domain) : Range :=
  function (base + increment) - function base - linear base increment - quadratic base increment increment

theorem cubicTaylorError_central_identity
    (function : Domain → Range) (linear : Domain → Domain →L[ℝ] Range)
    (quadratic : Domain → Domain →L[ℝ] Domain →L[ℝ] Range) (first second step : Domain) :
    (2 : ℝ) • ((quadratic second - quadratic first) step step) =
      cubicTaylorError function linear quadratic first ((second - first) + step) +
      cubicTaylorError function linear quadratic first ((second - first) - step) -
      (2 : ℝ) • cubicTaylorError function linear quadratic first (second - first) -
      cubicTaylorError function linear quadratic second step -
      cubicTaylorError function linear quadratic second (-step) := by
  have plus : first + ((second - first) + step) = second + step := by abel
  have minus : first + ((second - first) - step) = second + -step := by abel
  have center : first + (second - first) = second := by abel
  unfold cubicTaylorError
  rw [plus, minus, center]
  simp only [map_add, map_sub, map_neg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]
  module

theorem norm_five_term_difference_le (first second center fourth fifth : Range) :
    ‖first + second - (2 : ℝ) • center - fourth - fifth‖ ≤
      ‖first‖ + ‖second‖ + 2 * ‖center‖ + ‖fourth‖ + ‖fifth‖ := by
  have top := norm_sub_le (first + second - (2 : ℝ) • center - fourth) fifth
  have middle := norm_sub_le (first + second - (2 : ℝ) • center) fourth
  have bottom := norm_sub_le (first + second) ((2 : ℝ) • center)
  have sum := norm_add_le first second
  rw [norm_smul, Real.norm_eq_abs] at bottom
  norm_num at bottom
  linarith

end

end EulerNonuniqueness.General
