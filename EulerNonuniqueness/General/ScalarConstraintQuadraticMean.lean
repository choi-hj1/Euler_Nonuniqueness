import Mathlib

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem scalar_constraint_quadratic_mean_bound
    (function : Space → ℝ) (linear : Space →L[ℝ] ℝ)
    (base relative transverse basis : Space) {mean lower constant : ℝ}
    (lowerPositive : 0 < lower) (coefficientBound : lower ≤ linear basis)
    (decomposition : relative = transverse + mean • basis) (transverseZero : linear transverse = 0)
    (sameValue : function (base + relative) = function base)
    (remainderBound : ‖function (base + relative) - function base - linear relative‖ ≤ constant * ‖relative‖ ^ 2) :
    |mean| ≤ (constant / lower) * ‖relative‖ ^ 2 := by
  have derivativeIdentity : linear relative = mean * linear basis := by
    rw [decomposition, map_add, map_smul, transverseZero, zero_add]
    rfl
  have bound : |mean| * linear basis ≤ constant * ‖relative‖ ^ 2 := by
    simpa only [sameValue, sub_self, zero_sub, Real.norm_eq_abs, abs_neg, derivativeIdentity,
      abs_mul, abs_of_nonneg (lowerPositive.le.trans coefficientBound)] using remainderBound
  have weighted : |mean| * lower ≤ constant * ‖relative‖ ^ 2 :=
    (mul_le_mul_of_nonneg_left coefficientBound (abs_nonneg mean)).trans bound
  have divided := (le_div_iff₀ lowerPositive).mpr weighted
  convert divided using 1 <;> ring

end EulerNonuniqueness.General
