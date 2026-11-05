import EulerNonuniqueness.Section3.DiskChartedRelativeTaylor
import EulerNonuniqueness.General.IncrementTaylorFromSecondRegularity

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] diskChartedEulerRealSpace diskChartedEulerOperatorGroup diskChartedEulerOperatorSpace
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerUniformGroup diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete
  chartedUniformBilinearAddCommGroup chartedUniformBilinearAddCommMonoid chartedUniformBilinearModule
  chartedUniformThirdGroup chartedUniformThirdSpace
  chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd chartedBilinearGroup chartedBilinearModule

theorem diskChartedEulerTaylorRemainder_exists_increment_quadratic_ball :
    ∃ radius : ℝ, 0 < radius ∧ ∃ constant : NNReal,
      ∀ base initial final : PeriodicC1HolderHalf,
        ‖base‖ + (‖initial‖ + ‖final‖) ≤ radius →
        ‖diskChartedEulerTaylorRemainder base initial - diskChartedEulerTaylorRemainder base final‖ ≤
          (constant : ℝ) * (‖initial‖ + ‖final‖) ^ 2 * ‖initial - final‖ := by
  have originalTwice := diskChartedEulerField_eventually_twice_differentiable
  have first := originalTwice.mono (fun _ actual => actual.1)
  have regular := diskChartedEulerField_derivative_hasLipschitzSecondDerivativeNear.1
  have quadraticApply := diskMovingQuadraticBilinear_apply
  dsimp only [diskChartedEulerTaylorRemainder]
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_increment_quadratic_taylor_ball
      (Space := PeriodicC1HolderHalf) diskChartedEulerField diskMovingQuadraticBilinear first regular quadraticApply

theorem diskChartedEulerTaylorRemainder_exists_relative_cubic_ball :
    ∃ radius : ℝ, 0 < radius ∧ ∃ constant : NNReal,
      ∀ initialBase finalBase initialIncrement finalIncrement : PeriodicC1HolderHalf,
        ‖initialBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
        ‖finalBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
        ‖diskChartedEulerTaylorRemainder initialBase initialIncrement -
          diskChartedEulerTaylorRemainder finalBase finalIncrement‖ ≤
          (constant : ℝ) * ((‖initialIncrement‖ + ‖finalIncrement‖) ^ 2 *
            ‖initialIncrement - finalIncrement‖ + ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 3) := by
  obtain ⟨parameterRadius, parameterPositive, parameterConstant, parameterBound⟩ :=
    diskChartedEulerTaylorRemainder_exists_parameter_lipschitz_cubic_ball
  obtain ⟨incrementRadius, incrementPositive, incrementConstant, incrementBound⟩ :=
    diskChartedEulerTaylorRemainder_exists_increment_quadratic_ball
  refine ⟨min parameterRadius incrementRadius, lt_min parameterPositive incrementPositive,
    max parameterConstant incrementConstant, ?_⟩
  intro initialBase finalBase initialIncrement finalIncrement initialInside finalInside
  have initialIncrementInside : ‖initialBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ incrementRadius :=
    initialInside.trans (min_le_right _ _)
  have initialParameterInside : ‖initialBase‖ + ‖finalIncrement‖ ≤ parameterRadius := by
    have bound := initialInside.trans (min_le_left parameterRadius incrementRadius)
    have nonnegative := norm_nonneg initialIncrement
    linarith
  have finalParameterInside : ‖finalBase‖ + ‖finalIncrement‖ ≤ parameterRadius := by
    have bound := finalInside.trans (min_le_left parameterRadius incrementRadius)
    have nonnegative := norm_nonneg initialIncrement
    linarith
  have incrementEstimate := incrementBound initialBase initialIncrement finalIncrement initialIncrementInside
  have parameterEstimate := parameterBound initialBase finalBase finalIncrement initialParameterInside finalParameterInside
  have incrementCoefficient : (incrementConstant : ℝ) ≤ (max parameterConstant incrementConstant : NNReal) := by
    exact_mod_cast le_max_right parameterConstant incrementConstant
  have parameterCoefficient : (parameterConstant : ℝ) ≤ (max parameterConstant incrementConstant : NNReal) := by
    exact_mod_cast le_max_left parameterConstant incrementConstant
  have split := norm_sub_le_norm_sub_add_norm_sub
    (diskChartedEulerTaylorRemainder initialBase initialIncrement)
    (diskChartedEulerTaylorRemainder initialBase finalIncrement)
    (diskChartedEulerTaylorRemainder finalBase finalIncrement)
  apply (split.trans (add_le_add incrementEstimate parameterEstimate)).trans
  calc
    _ = (incrementConstant : ℝ) * ((‖initialIncrement‖ + ‖finalIncrement‖) ^ 2 *
          ‖initialIncrement - finalIncrement‖) +
        (parameterConstant : ℝ) * (‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 3) := by ring
    _ ≤ (max parameterConstant incrementConstant : NNReal) *
          ((‖initialIncrement‖ + ‖finalIncrement‖) ^ 2 * ‖initialIncrement - finalIncrement‖) +
        (max parameterConstant incrementConstant : NNReal) *
          (‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 3) :=
      add_le_add (mul_le_mul_of_nonneg_right incrementCoefficient (by positivity))
        (mul_le_mul_of_nonneg_right parameterCoefficient (by positivity))
    _ = _ := by ring

end

end EulerNonuniqueness.Paper
