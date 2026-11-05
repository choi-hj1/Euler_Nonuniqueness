import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace EulerNonuniqueness.General

theorem exists_uniform_reciprocal_quadratic_small
    {quadratic linear tolerance : ℝ} (quadraticNonnegative : 0 ≤ quadratic)
    (tolerancePositive : 0 < tolerance) :
    ∃ threshold ≥ (2 : ℝ), ∀ parameter : ℝ, threshold ≤ parameter →
      quadratic / parameter ^ 2 + linear / parameter ≤ tolerance := by
  refine ⟨max 2 ((quadratic + linear) / tolerance), le_max_left _ _, ?_⟩
  intro parameter parameterBound
  have parameterTwo : 2 ≤ parameter := (le_max_left _ _).trans parameterBound
  have parameterOne : 1 ≤ parameter := (by norm_num : (1 : ℝ) ≤ 2).trans parameterTwo
  have parameterPositive : 0 < parameter := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) parameterTwo
  have squareBound : parameter ≤ parameter ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left parameterOne parameterPositive.le]
  have quadraticBound := div_le_div_of_nonneg_left quadraticNonnegative parameterPositive squareBound
  have numeratorBound : quadratic + linear ≤ tolerance * parameter := by
    have actual := (div_le_iff₀ tolerancePositive).mp ((le_max_right _ _).trans parameterBound)
    simpa only [mul_comm] using actual
  calc
    _ ≤ quadratic / parameter + linear / parameter := add_le_add_right quadraticBound _
    _ = (quadratic + linear) / parameter := by ring
    _ ≤ tolerance := (div_le_iff₀ parameterPositive).mpr (by simpa only [mul_comm] using numeratorBound)

end EulerNonuniqueness.General
