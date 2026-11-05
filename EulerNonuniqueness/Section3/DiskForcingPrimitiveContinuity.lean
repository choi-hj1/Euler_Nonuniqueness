import EulerNonuniqueness.Section3.DiskForcingPrimitiveSeries
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance primitiveContinuityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem diskForcingPrimitive_continuousAt (degree : ℕ) (frequency : ℝ)
    {amplitude : ℝ → ℂ} {time : ℝ} (continuous : ContinuousAt amplitude time) :
    ContinuousAt (diskForcingPrimitive degree frequency amplitude) time := by
  have phase := (diskForcingPhase_hasDerivAt degree frequency time).continuousAt
  exact ((continuousAt_const.mul continuous).mul phase).smul continuousAt_const

theorem diskForcingPrimitive_tsum_continuousAt_of_weighted_bound
    {frequency time : ℝ} (nonzero : frequency ≠ 0)
    (amplitude : ℕ → ℝ → ℂ) (bound : ℕ → ℝ)
    (continuous : ∀ degree, ContinuousAt (amplitude degree) time)
    (weighted : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * bound degree))
    (dominates : ∀ᶠ current in 𝓝 time, ∀ degree, ‖amplitude degree current‖ ≤ bound degree) :
    ContinuousAt (fun current => ∑' degree, diskForcingPrimitive degree frequency (amplitude degree) current) time := by
  apply tendsto_tsum_of_dominated_convergence
    (weighted.mul_left (4 / |frequency|))
    (fun degree => (diskForcingPrimitive_continuousAt degree frequency (continuous degree)).tendsto)
  filter_upwards [dominates] with current bounded
  intro degree
  apply (diskForcingPrimitive_weighted_bound degree nonzero (amplitude degree) current).trans
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (bounded degree) (by positivity)) (by positivity)

end EulerNonuniqueness.Paper
