import EulerNonuniqueness.Section6.CoherentPointShapeChart
import Mathlib.Data.Real.Pi.Bounds

noncomputable section

namespace EulerNonuniqueness.Section6

theorem pointShapeChart_leftHalfPlane_of_small {positive negative : ℂ}
    (positiveNonzero : positive ≠ 0) (negativeNonzero : negative ≠ 0)
    (small : |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| ≤ 1 / 4) :
    (((negative / positive) ^ 2) : ℂ).re < 0 := by
  let point := pointShapeChart positive negative
  let quotient := (negative / positive) ^ 2
  have reconstruction := (shapeChart_reconstruction (pointShapeRatio positive negative)
    (pointShapeAngle positive negative)).2
  change Real.pi + Real.sqrt 2 * (point.1 - point.2) = unwrappedShapeArgument quotient at reconstruction
  have differenceBound : |point.1 - point.2| ≤ 1 / 4 := (abs_sub _ _).trans small
  have sqrtBound : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have displacementBound : |Real.sqrt 2 * (point.1 - point.2)| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have control := mul_le_mul sqrtBound differenceBound (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at control ⊢
    exact control
  have lower : Real.pi / 2 < unwrappedShapeArgument quotient := by
    rw [← reconstruction]
    linarith [(abs_le.mp displacementBound).1, Real.pi_gt_three]
  have upper : unwrappedShapeArgument quotient < Real.pi + Real.pi / 2 := by
    rw [← reconstruction]
    linarith [(abs_le.mp displacementBound).2, Real.pi_gt_three]
  have cosineNegative := Real.cos_neg_of_pi_div_two_lt_of_lt lower upper
  have cosineIdentity : Real.cos (unwrappedShapeArgument quotient) = Real.cos quotient.arg := by
    unfold unwrappedShapeArgument
    split_ifs <;> simp only [Real.cos_add_two_pi]
  rw [cosineIdentity] at cosineNegative
  have nonzero : quotient ≠ 0 := pow_ne_zero 2 (div_ne_zero negativeNonzero positiveNonzero)
  rw [← Complex.norm_mul_cos_arg quotient]
  exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr nonzero) cosineNegative

end EulerNonuniqueness.Section6
