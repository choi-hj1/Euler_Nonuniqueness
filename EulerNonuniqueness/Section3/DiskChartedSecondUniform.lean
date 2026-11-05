import EulerNonuniqueness.Section3.DiskChartedSecondLipschitz
import EulerNonuniqueness.Section3.DiskChartedSecondDifferentiable

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter Metric
open scoped Topology

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] diskChartedEulerRealSpace diskChartedEulerOperatorGroup diskChartedEulerOperatorSpace
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerUniformGroup diskChartedEulerOperatorComplete
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd

theorem diskChartedEulerField_exists_second_lipschitz_ball :
    ∃ radius : ℝ, 0 < radius ∧ ∃ constant : NNReal,
      (∀ data ∈ closedBall (0 : PeriodicC1HolderHalf) radius,
        DifferentiableAt ℝ diskChartedEulerField data ∧
        DifferentiableAt ℝ (fderiv ℝ diskChartedEulerField) data) ∧
      LipschitzOnWith constant (fderiv ℝ (fderiv ℝ diskChartedEulerField))
        (closedBall (0 : PeriodicC1HolderHalf) radius) := by
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ :=
    diskChartedEulerField_derivative_hasLipschitzDerivativeNear.2
  have combined : neighborhood ∩ {data | DifferentiableAt ℝ diskChartedEulerField data ∧
      DifferentiableAt ℝ (fderiv ℝ diskChartedEulerField) data} ∈ 𝓝 (0 : PeriodicC1HolderHalf) :=
    inter_mem nearby diskChartedEulerField_eventually_twice_differentiable
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp combined
  have smaller : closedBall (0 : PeriodicC1HolderHalf) (radius / 2) ⊆
      neighborhood ∩ {data | DifferentiableAt ℝ diskChartedEulerField data ∧
        DifferentiableAt ℝ (fderiv ℝ diskChartedEulerField) data} := by
    intro data member
    apply contained
    have bound := Metric.mem_closedBall.mp member
    apply Metric.mem_ball.mpr
    linarith
  refine ⟨radius / 2, by positivity, constant, ?_, lipschitz.mono ?_⟩
  · intro data member
    have regular : DifferentiableAt ℝ diskChartedEulerField data ∧
        DifferentiableAt ℝ (fderiv ℝ diskChartedEulerField) data := (smaller member).2
    exact regular
  · intro data member
    exact (smaller member).1

end

end EulerNonuniqueness.Paper
