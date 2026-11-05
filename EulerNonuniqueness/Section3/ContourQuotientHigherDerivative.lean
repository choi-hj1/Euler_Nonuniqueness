import EulerNonuniqueness.Section3.ContourQuotientAnalytic

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance quotientHigherHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance quotientHigherC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance quotientHigherOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance quotientHigherOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem analyticAt_contourQuotientDerivativeCLM (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    AnalyticAt ℝ contourQuotientDerivativeCLM data := by
  have actual := (analyticAt_extendedContourTangentQuotient data small).fderiv
  apply actual.congr
  have nearby : Metric.ball standardCircleBanach (min 1 (2 / (3 * Real.pi))) ∈ 𝓝 data :=
    Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_eq_norm data standardCircleBanach] using small)
  filter_upwards [nearby] with point member
  have point_small : ‖point - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    simpa only [Metric.mem_ball, dist_eq_norm point standardCircleBanach] using member
  exact (HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
    (hasFDerivAt_extendedContourTangentQuotient point point_small))

end

end EulerNonuniqueness.Paper
