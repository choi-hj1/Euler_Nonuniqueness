import EulerNonuniqueness.Section3.WeakHolomorphicCurve
import EulerNonuniqueness.Section3.ComplexHolderInstances

open Set Metric
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def complexHolderEvaluation (label : ℝ) : PeriodicHolderHalf →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun data : PeriodicHolderHalf => data.val.1 label
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun data => by simpa only [one_mul] using PeriodicHolderHalf.value_bound data label)

theorem analyticAt_holderCurve_of_evaluations {function : ℂ → PeriodicHolderHalf}
    {center : ℂ} {radius : ℝ≥0} (positive : 0 < radius)
    (continuous : ContinuousOn function (closedBall center radius))
    (holomorphic : ∀ label, DifferentiableOn ℂ (fun parameter => (function parameter).val.1 label)
      (ball center radius)) : AnalyticAt ℂ function center := by
  apply analyticAt_of_separating_evaluations complexHolderEvaluation
    (fun first second equal => PeriodicHolderHalf.ext_value equal) positive continuous holomorphic

def complexC1HolderEvaluation (label : ℝ) : PeriodicC1HolderHalf →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun data : PeriodicC1HolderHalf => data.val.1 label
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun data => by simpa only [one_mul] using PeriodicC1HolderHalf.value_bound data label)

theorem analyticAt_c1HolderCurve_of_evaluations {function : ℂ → PeriodicC1HolderHalf}
    {center : ℂ} {radius : ℝ≥0} (positive : 0 < radius)
    (continuous : ContinuousOn function (closedBall center radius))
    (holomorphic : ∀ label, DifferentiableOn ℂ (fun parameter => (function parameter).val.1 label)
      (ball center radius)) : AnalyticAt ℂ function center := by
  apply analyticAt_of_separating_evaluations complexC1HolderEvaluation
    (fun first second equal => PeriodicC1HolderHalf.ext_value equal) positive continuous holomorphic

end

end EulerNonuniqueness.Paper
