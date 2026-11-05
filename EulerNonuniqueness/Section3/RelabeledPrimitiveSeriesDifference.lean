import EulerNonuniqueness.Section3.RelabeledPrimitiveDifferenceBound
import EulerNonuniqueness.Section3.RelabeledForcingPrimitiveSeries

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance primitiveSeriesDifferenceC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem relabeledForcingPrimitiveSeries_difference_bound
    (first second : PeriodicC1HolderHalf)
    (firstSmall : ‖first‖ < 1 / 2) (secondSmall : ‖second‖ < 1 / 2)
    (firstReal : ∀ label, star (first.val.1 label) = first.val.1 label)
    (secondReal : ∀ label, star (second.val.1 label) = second.val.1 label)
    (firstBound : ‖diskRelabelCurve first 1‖ ≤ 3)
    (secondBound : ‖diskRelabelCurve second 1‖ ≤ 3)
    {frequency : ℝ} (nonzero : frequency ≠ 0) (amplitude : ℕ → ℝ → ℂ) (time : ℝ)
    (weighted : Summable (fun degree => (24 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖)) :
    ‖relabeledForcingPrimitiveSeries first frequency amplitude time -
      relabeledForcingPrimitiveSeries second frequency amplitude time‖ ≤
      (2 / |frequency|) * (∑' degree, (24 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖) *
        ‖diskRelabelCurve first 1 - diskRelabelCurve second 1‖ := by
  have weightedTwo : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖) :=
    Summable.of_nonneg_of_le (fun degree => by positivity)
      (fun degree => mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 24) _) (norm_nonneg _)) weighted
  have summableCircle := diskForcingPrimitive_summable nonzero amplitude time weightedTwo
  have summableFirst : Summable (fun degree => relabeledDiskForcingPrimitive first degree frequency (amplitude degree) time) := by
    have actual := (fixedRelabelEquivalence first firstSmall).toContinuousLinearMap.summable summableCircle
    simpa only [ContinuousLinearEquiv.coe_coe, fixedRelabelEquivalence_forcingPrimitive first firstSmall firstReal] using actual
  have summableSecond : Summable (fun degree => relabeledDiskForcingPrimitive second degree frequency (amplitude degree) time) := by
    have actual := (fixedRelabelEquivalence second secondSmall).toContinuousLinearMap.summable summableCircle
    simpa only [ContinuousLinearEquiv.coe_coe, fixedRelabelEquivalence_forcingPrimitive second secondSmall secondReal] using actual
  have summableBound := (weighted.mul_left (2 / |frequency|)).mul_right
    ‖diskRelabelCurve first 1 - diskRelabelCurve second 1‖
  have termBound := fun degree => relabeledDiskForcingPrimitive_difference_bound first second
    firstBound secondBound degree nonzero (amplitude degree) time
  have summableNorm : Summable (fun degree =>
      ‖relabeledDiskForcingPrimitive first degree frequency (amplitude degree) time -
        relabeledDiskForcingPrimitive second degree frequency (amplitude degree) time‖) :=
    Summable.of_nonneg_of_le (fun degree => norm_nonneg _) termBound summableBound
  unfold relabeledForcingPrimitiveSeries
  rw [← tsum_sub summableFirst summableSecond]
  calc
    _ ≤ ∑' degree, (2 / |frequency|) * ((24 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖) *
        ‖diskRelabelCurve first 1 - diskRelabelCurve second 1‖ :=
      (norm_tsum_le_tsum_norm summableNorm).trans
        (Summable.tsum_le_tsum termBound summableNorm summableBound)
    _ = _ := by rw [tsum_mul_right, tsum_mul_left]

end EulerNonuniqueness.Paper
