import EulerNonuniqueness.Section3.DiskChartedThirdUniform
import EulerNonuniqueness.Section3.DiskMovingQuadraticTaylor
import EulerNonuniqueness.General.RelativeTaylorFromThirdRegularity

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
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance relativeTaylorEndAddCommMonoid : AddCommMonoid
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  diskChartedEulerOperatorGroup.toAddCommGroup.toAddCommMonoid
local instance relativeTaylorEndModule : Module ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  diskChartedEulerOperatorSpace.toModule

def diskChartedEulerTaylorRemainder (data increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskChartedEulerField (data + increment) - diskChartedEulerField data -
    fderiv ℝ diskChartedEulerField data increment - diskMovingQuadraticBilinear data increment increment

theorem diskChartedEulerTaylorRemainder_exists_parameter_lipschitz_cubic_ball :
    ∃ radius : ℝ, 0 < radius ∧ ∃ constant : NNReal,
      ∀ initial final increment : PeriodicC1HolderHalf,
        ‖initial‖ + ‖increment‖ ≤ radius → ‖final‖ + ‖increment‖ ≤ radius →
        ‖diskChartedEulerTaylorRemainder initial increment - diskChartedEulerTaylorRemainder final increment‖ ≤
          (constant : ℝ) * ‖initial - final‖ * ‖increment‖ ^ 3 := by
  have originalTwice := diskChartedEulerField_eventually_twice_differentiable
  have first := originalTwice.mono (fun _ actual => actual.1)
  have regular := diskChartedEulerField_derivative_hasLipschitzSecondDerivativeNear
  have quadraticApply := diskMovingQuadraticBilinear_apply
  dsimp only [diskChartedEulerTaylorRemainder]
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_parameter_lipschitz_cubic_taylor_ball
      (Space := PeriodicC1HolderHalf) diskChartedEulerField diskMovingQuadraticBilinear
      first regular quadraticApply

end

end EulerNonuniqueness.Paper
