import EulerNonuniqueness.Section3.DiskChartedThirdLipschitz
import EulerNonuniqueness.Section3.DiskChartedSecondDifferentiable
import EulerNonuniqueness.General.RelativeCubicTaylor
import EulerNonuniqueness.General.LocalThirdUniformBall

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] diskChartedEulerRealSpace diskChartedEulerOperatorGroup diskChartedEulerOperatorSpace
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerUniformGroup diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete

local instance chartedUniformBilinearAddCommGroup : AddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  chartedThirdBilinearGroup.toAddCommGroup
local instance chartedUniformBilinearAddCommMonoid : AddCommMonoid
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  chartedUniformBilinearAddCommGroup.toAddCommMonoid
local instance chartedUniformBilinearModule : Module ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  chartedThirdBilinearSpace.toModule

local instance chartedUniformThirdGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance chartedUniformThirdSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem diskChartedEulerField_exists_third_lipschitz_ball :
    ∃ radius : ℝ, 0 < radius ∧ ∃ constant : NNReal,
      (∀ data ∈ closedBall (0 : PeriodicC1HolderHalf) radius,
        DifferentiableAt ℝ diskChartedEulerField data ∧
        DifferentiableAt ℝ (fderiv ℝ diskChartedEulerField) data ∧
        DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ diskChartedEulerField)) data) ∧
      LipschitzOnWith constant (fderiv ℝ (fderiv ℝ (fderiv ℝ diskChartedEulerField)))
        (closedBall (0 : PeriodicC1HolderHalf) radius) := by
  have originalTwice := diskChartedEulerField_eventually_twice_differentiable
  have first := originalTwice.mono (fun _ regular => regular.1)
  have regular := diskChartedEulerField_derivative_hasLipschitzSecondDerivativeNear
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_third_lipschitz_closedBall
      (Space := PeriodicC1HolderHalf) diskChartedEulerField (0 : PeriodicC1HolderHalf) first regular

end

end EulerNonuniqueness.Paper
