import EulerNonuniqueness.Section3.DiskForcingWeightedPrimitive
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] forcingModeC1RealSpace

local instance forcingSeriesC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskForcingPrimitive_summable {frequency : ℝ} (nonzero : frequency ≠ 0)
    (amplitude : ℕ → ℝ → ℂ) (time : ℝ)
    (weighted : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖)) :
    Summable (fun degree => diskForcingPrimitive degree frequency (amplitude degree) time) := by
  exact Summable.of_norm_bounded
    (fun degree => (4 / |frequency|) * ((2 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖))
    (weighted.mul_left (4 / |frequency|))
    (fun degree => diskForcingPrimitive_weighted_bound degree nonzero (amplitude degree) time)

theorem diskForcingPrimitive_tsum_norm_bound {frequency : ℝ} (nonzero : frequency ≠ 0)
    (amplitude : ℕ → ℝ → ℂ) (time : ℝ)
    (weighted : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖)) :
    ‖∑' degree, diskForcingPrimitive degree frequency (amplitude degree) time‖ ≤
      (4 / |frequency|) * ∑' degree, (2 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖ := by
  have bound := tsum_of_norm_bounded (weighted.mul_left (4 / |frequency|)).hasSum
    (fun degree => diskForcingPrimitive_weighted_bound degree nonzero (amplitude degree) time)
  simpa only [tsum_mul_left] using bound

end

end EulerNonuniqueness.Paper
