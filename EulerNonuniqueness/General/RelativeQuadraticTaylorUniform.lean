import EulerNonuniqueness.General.RelativeQuadraticFromSecondRegularity
import EulerNonuniqueness.General.QuadraticTaylorIncrementDifference

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem exists_relative_quadratic_taylor_ball (function : Space → Target)
    (regular : HasLipschitzSecondDerivativeNear function (0 : Space)) :
    ∃ radius > 0, ∃ constant : NNReal, ∀ initialBase finalBase initialIncrement finalIncrement : Space,
      ‖initialBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖(function (initialBase + initialIncrement) - function initialBase -
          fderiv ℝ function initialBase initialIncrement) -
        (function (finalBase + finalIncrement) - function finalBase -
          fderiv ℝ function finalBase finalIncrement)‖ ≤ (constant : ℝ) *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2) := by
  obtain ⟨parameterRadius, parameterPositive, parameterConstant, parameterBound⟩ :=
    exists_parameter_lipschitz_quadratic_taylor_ball function regular
  obtain ⟨incrementRadius, incrementPositive, incrementConstant, incrementBound⟩ :=
    exists_increment_linear_quadratic_taylor_ball function regular.1
  refine ⟨min parameterRadius incrementRadius, lt_min parameterPositive incrementPositive,
    max parameterConstant incrementConstant, ?_⟩
  intro initialBase finalBase initialIncrement finalIncrement initialInside finalInside
  have incrementInside := initialInside.trans (min_le_right parameterRadius incrementRadius)
  have initialParameter : ‖initialBase‖ + ‖finalIncrement‖ ≤ parameterRadius := by
    have bound := initialInside.trans (min_le_left parameterRadius incrementRadius)
    linarith [norm_nonneg initialIncrement]
  have finalParameter : ‖finalBase‖ + ‖finalIncrement‖ ≤ parameterRadius := by
    have bound := finalInside.trans (min_le_left parameterRadius incrementRadius)
    linarith [norm_nonneg initialIncrement]
  have incrementEstimate := incrementBound initialBase initialIncrement finalIncrement incrementInside
  have parameterEstimate := parameterBound initialBase finalBase finalIncrement initialParameter finalParameter
  have incrementCoefficient : (incrementConstant : ℝ) ≤ (max parameterConstant incrementConstant : NNReal) := by
    exact_mod_cast le_max_right parameterConstant incrementConstant
  have parameterCoefficient : (parameterConstant : ℝ) ≤ (max parameterConstant incrementConstant : NNReal) := by
    exact_mod_cast le_max_left parameterConstant incrementConstant
  have split := norm_sub_le_norm_sub_add_norm_sub
    (function (initialBase + initialIncrement) - function initialBase - fderiv ℝ function initialBase initialIncrement)
    (function (initialBase + finalIncrement) - function initialBase - fderiv ℝ function initialBase finalIncrement)
    (function (finalBase + finalIncrement) - function finalBase - fderiv ℝ function finalBase finalIncrement)
  apply (split.trans (add_le_add incrementEstimate parameterEstimate)).trans
  calc
    _ = (incrementConstant : ℝ) * ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖) +
        (parameterConstant : ℝ) * (‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2) := by ring
    _ ≤ (max parameterConstant incrementConstant : NNReal) *
          ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖) +
        (max parameterConstant incrementConstant : NNReal) * (‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_right incrementCoefficient (by positivity))
        (mul_le_mul_of_nonneg_right parameterCoefficient (by positivity))
    _ = _ := by ring

end

end EulerNonuniqueness.General
