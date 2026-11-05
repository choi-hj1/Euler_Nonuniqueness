import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

namespace EulerNonuniqueness.General

/-- A fixed positive hit of an exponential profile occurs after any prescribed exponent
once its seed is sufficiently small. -/
theorem exponent_gt_of_fixed_level_exponential_profile
    {level seed magnitude exponent bound : ℝ}
    (seedPositive : 0 < seed)
    (magnitudeNonnegative : 0 ≤ magnitude)
    (profile : level ≤ magnitude * seed * Real.exp exponent)
    (seedSmall : seed < level * Real.exp (-bound) / (magnitude + 1)) :
    bound < exponent := by
  by_contra! exponentBound
  have denominatorPositive : 0 < magnitude + 1 := by linarith only [magnitudeNonnegative]
  have scaledSeed := (lt_div_iff₀ denominatorPositive).mp seedSmall
  have scaled := mul_lt_mul_of_pos_right scaledSeed (Real.exp_pos bound)
  have cancellation : level * Real.exp (-bound) * Real.exp bound = level := by
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  rw [cancellation] at scaled
  have exponentialBound := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponentBound)
    (mul_nonneg magnitudeNonnegative seedPositive.le)
  have strict : magnitude * seed * Real.exp bound < level := by
    nlinarith only [scaled, mul_pos seedPositive (Real.exp_pos bound)]
  exact (not_lt_of_ge (profile.trans exponentialBound)) strict

end EulerNonuniqueness.General
