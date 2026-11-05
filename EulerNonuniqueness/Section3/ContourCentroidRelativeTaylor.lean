import EulerNonuniqueness.Section3.ContourCentroidTangentQuadratic
import EulerNonuniqueness.General.RelativeQuadraticFromSecondRegularity
import EulerNonuniqueness.General.QuadraticTaylorIncrementDifference

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance centroidRelativeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph
local instance centroidRelativeC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def contourCentroidOffset (increment : PeriodicC1HolderHalf) : ℂ :=
  contourCentroidFunctional (standardCircleBanach + increment)

theorem contourCentroidOffset_analyticAt_zero : AnalyticAt ℝ contourCentroidOffset 0 := by
  have atCircle : AnalyticAt ℝ contourCentroidFunctional standardCircleBanach :=
    analyticAt_contourCentroidFunctional _ (by simp only [sub_self, norm_zero]; norm_num)
  have translation : AnalyticAt ℝ (fun increment : PeriodicC1HolderHalf => standardCircleBanach + increment) 0 :=
    analyticAt_const.add analyticAt_id
  exact AnalyticAt.comp_of_eq (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
    (G := ℂ) atCircle translation (by simp)

def contourCentroidTaylorRemainder (base increment : PeriodicC1HolderHalf) : ℂ :=
  contourCentroidOffset (base + increment) - contourCentroidOffset base -
    fderiv ℝ contourCentroidOffset base increment

theorem contourCentroidTaylorRemainder_exists_parameter_lipschitz_quadratic_ball :
    ∃ radius > 0, ∃ constant : NNReal, ∀ initial final increment : PeriodicC1HolderHalf,
      ‖initial‖ + ‖increment‖ ≤ radius → ‖final‖ + ‖increment‖ ≤ radius →
      ‖contourCentroidTaylorRemainder initial increment - contourCentroidTaylorRemainder final increment‖ ≤
        (constant : ℝ) * ‖initial - final‖ * ‖increment‖ ^ 2 := by
  have regular := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_of_analyticAt
    contourCentroidOffset_analyticAt_zero
  unfold contourCentroidTaylorRemainder
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_parameter_lipschitz_quadratic_taylor_ball
      (Space := PeriodicC1HolderHalf) (Target := ℂ) contourCentroidOffset regular

theorem contourCentroidTaylorRemainder_exists_increment_linear_ball :
    ∃ radius > 0, ∃ constant : NNReal, ∀ base initial final : PeriodicC1HolderHalf,
      ‖base‖ + (‖initial‖ + ‖final‖) ≤ radius →
      ‖contourCentroidTaylorRemainder base initial - contourCentroidTaylorRemainder base final‖ ≤
        (constant : ℝ) * (‖initial‖ + ‖final‖) * ‖initial - final‖ := by
  have regular := EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt
    contourCentroidOffset_analyticAt_zero
  unfold contourCentroidTaylorRemainder
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_increment_linear_quadratic_taylor_ball
      (Space := PeriodicC1HolderHalf) (Target := ℂ) contourCentroidOffset regular

theorem contourCentroidTaylorRemainder_exists_relative_quadratic_ball :
    ∃ radius > 0, ∃ constant : NNReal,
      ∀ initialBase finalBase initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖initialBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖contourCentroidTaylorRemainder initialBase initialIncrement -
        contourCentroidTaylorRemainder finalBase finalIncrement‖ ≤ (constant : ℝ) *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2) := by
  obtain ⟨parameterRadius, parameterPositive, parameterConstant, parameterBound⟩ :=
    contourCentroidTaylorRemainder_exists_parameter_lipschitz_quadratic_ball
  obtain ⟨incrementRadius, incrementPositive, incrementConstant, incrementBound⟩ :=
    contourCentroidTaylorRemainder_exists_increment_linear_ball
  refine ⟨min parameterRadius incrementRadius, lt_min parameterPositive incrementPositive,
    max parameterConstant incrementConstant, ?_⟩
  intro initialBase finalBase initialIncrement finalIncrement initialInside finalInside
  have incrementInside : ‖initialBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ incrementRadius :=
    initialInside.trans (min_le_right _ _)
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
    (contourCentroidTaylorRemainder initialBase initialIncrement)
    (contourCentroidTaylorRemainder initialBase finalIncrement)
    (contourCentroidTaylorRemainder finalBase finalIncrement)
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

end EulerNonuniqueness.Paper
