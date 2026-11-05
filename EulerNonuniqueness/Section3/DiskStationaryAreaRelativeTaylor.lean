import EulerNonuniqueness.Section3.DiskStationaryArea
import EulerNonuniqueness.General.RelativeQuadraticFromSecondRegularity
import EulerNonuniqueness.General.QuadraticTaylorIncrementDifference

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance stationaryRelativeGroup : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] stationaryAreaHolderSpace stationaryAreaC1Space

def diskStationaryAreaTaylorRemainder (base increment : PeriodicC1HolderHalf) : ℝ :=
  diskStationaryArea (base + increment) - diskStationaryArea base -
    fderiv ℝ diskStationaryArea base increment

theorem diskStationaryAreaTaylorRemainder_exists_parameter_lipschitz_quadratic_ball :
    ∃ radius > 0, ∃ constant : NNReal, ∀ initial final increment : PeriodicC1HolderHalf,
      ‖initial‖ + ‖increment‖ ≤ radius → ‖final‖ + ‖increment‖ ≤ radius →
      |diskStationaryAreaTaylorRemainder initial increment - diskStationaryAreaTaylorRemainder final increment| ≤
        (constant : ℝ) * ‖initial - final‖ * ‖increment‖ ^ 2 := by
  have analytic := diskStationaryArea_analyticAt (0 : PeriodicC1HolderHalf)
  have regular := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_of_analyticAt analytic
  dsimp only [diskStationaryAreaTaylorRemainder]
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_parameter_lipschitz_quadratic_taylor_ball
      (Space := PeriodicC1HolderHalf) (Target := ℝ) diskStationaryArea regular

theorem diskStationaryAreaTaylorRemainder_exists_increment_linear_ball :
    ∃ radius > 0, ∃ constant : NNReal, ∀ base initial final : PeriodicC1HolderHalf,
      ‖base‖ + (‖initial‖ + ‖final‖) ≤ radius →
      |diskStationaryAreaTaylorRemainder base initial - diskStationaryAreaTaylorRemainder base final| ≤
        (constant : ℝ) * (‖initial‖ + ‖final‖) * ‖initial - final‖ := by
  have analytic := diskStationaryArea_analyticAt (0 : PeriodicC1HolderHalf)
  have regular := EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt analytic
  dsimp only [diskStationaryAreaTaylorRemainder]
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_increment_linear_quadratic_taylor_ball
      (Space := PeriodicC1HolderHalf) (Target := ℝ) diskStationaryArea regular

theorem diskStationaryAreaTaylorRemainder_exists_relative_quadratic_ball :
    ∃ radius > 0, ∃ constant : NNReal, ∀ initialBase finalBase initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖initialBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      |diskStationaryAreaTaylorRemainder initialBase initialIncrement -
        diskStationaryAreaTaylorRemainder finalBase finalIncrement| ≤ (constant : ℝ) *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2) := by
  obtain ⟨parameterRadius, parameterPositive, parameterConstant, parameterBound⟩ :=
    diskStationaryAreaTaylorRemainder_exists_parameter_lipschitz_quadratic_ball
  obtain ⟨incrementRadius, incrementPositive, incrementConstant, incrementBound⟩ :=
    diskStationaryAreaTaylorRemainder_exists_increment_linear_ball
  refine ⟨min parameterRadius incrementRadius, lt_min parameterPositive incrementPositive,
    max parameterConstant incrementConstant, ?_⟩
  intro initialBase finalBase initialIncrement finalIncrement initialInside finalInside
  have incrementInside : ‖initialBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ incrementRadius :=
    initialInside.trans (min_le_right _ _)
  have initialParameter : ‖initialBase‖ + ‖finalIncrement‖ ≤ parameterRadius := by
    have bound := initialInside.trans (min_le_left parameterRadius incrementRadius)
    have nonnegative := norm_nonneg initialIncrement
    linarith
  have finalParameter : ‖finalBase‖ + ‖finalIncrement‖ ≤ parameterRadius := by
    have bound := finalInside.trans (min_le_left parameterRadius incrementRadius)
    have nonnegative := norm_nonneg initialIncrement
    linarith
  have incrementEstimate := incrementBound initialBase initialIncrement finalIncrement incrementInside
  have parameterEstimate := parameterBound initialBase finalBase finalIncrement initialParameter finalParameter
  have incrementCoefficient : (incrementConstant : ℝ) ≤ (max parameterConstant incrementConstant : NNReal) := by
    exact_mod_cast le_max_right parameterConstant incrementConstant
  have parameterCoefficient : (parameterConstant : ℝ) ≤ (max parameterConstant incrementConstant : NNReal) := by
    exact_mod_cast le_max_left parameterConstant incrementConstant
  have split : |diskStationaryAreaTaylorRemainder initialBase initialIncrement -
      diskStationaryAreaTaylorRemainder finalBase finalIncrement| ≤
      |diskStationaryAreaTaylorRemainder initialBase initialIncrement -
        diskStationaryAreaTaylorRemainder initialBase finalIncrement| +
      |diskStationaryAreaTaylorRemainder initialBase finalIncrement -
        diskStationaryAreaTaylorRemainder finalBase finalIncrement| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le_norm_sub_add_norm_sub
      (diskStationaryAreaTaylorRemainder initialBase initialIncrement)
      (diskStationaryAreaTaylorRemainder initialBase finalIncrement)
      (diskStationaryAreaTaylorRemainder finalBase finalIncrement)
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
