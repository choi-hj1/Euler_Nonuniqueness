import EulerNonuniqueness.Section3.DiskForcingSeriesWeightedDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance forcingSeriesEquationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

def diskForcingTerm (degree : ℕ) (frequency : ℝ) (amplitude : ℝ → ℂ) (time : ℝ) : PeriodicC1HolderHalf :=
  (amplitude time * diskForcingPhase degree frequency time) • c1Conjugate (diskCircleMode (degree + 1))

theorem diskForcingTerm_norm_bound (degree : ℕ) (frequency : ℝ) (amplitude : ℝ → ℂ) (time : ℝ) :
    ‖diskForcingTerm degree frequency amplitude time‖ ≤ 8 * ((2 : ℝ) ^ (degree + 1) * ‖amplitude time‖) := by
  unfold diskForcingTerm
  rw [norm_smul, norm_mul, diskForcingPhase_norm, mul_one]
  have result := mul_le_mul_of_nonneg_left (diskCircleMode_geometric_norm_bound degree) (norm_nonneg (amplitude time))
  convert result using 1 <;> ring

theorem diskForcingTerm_summable (frequency : ℝ) (amplitude : ℕ → ℝ → ℂ) (time : ℝ)
    (weighted : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖)) :
    Summable (fun degree => diskForcingTerm degree frequency (amplitude degree) time) :=
  Summable.of_norm_bounded _ (weighted.mul_left 8)
    (fun degree => diskForcingTerm_norm_bound degree frequency (amplitude degree) time)

theorem diskForcingPrimitiveJet_tsum_eq {frequency : ℝ} (nonzero : frequency ≠ 0)
    (amplitude amplitudeDerivative : ℕ → ℝ → ℂ) (time : ℝ)
    (weighted : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖))
    (weightedDerivative : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * ‖amplitudeDerivative degree time‖)) :
    (∑' degree, diskForcingPrimitiveJet degree frequency (amplitude degree) (amplitudeDerivative degree) time) =
      frequency • diskRotatingDerivative (∑' degree, diskForcingPrimitive degree frequency (amplitude degree) time) +
      (∑' degree, diskForcingTerm degree frequency (amplitude degree) time) +
      (∑' degree, diskForcingPrimitive degree frequency (amplitudeDerivative degree) time) := by
  let rate : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf := frequency • diskRotatingDerivative
  have primitiveSummable := diskForcingPrimitive_summable nonzero amplitude time weighted
  have derivativeSummable := diskForcingPrimitive_summable nonzero amplitudeDerivative time weightedDerivative
  have forceSummable := diskForcingTerm_summable frequency amplitude time weighted
  have linearSummable := rate.summable primitiveSummable
  change (∑' degree, ((rate (diskForcingPrimitive degree frequency (amplitude degree) time) +
    diskForcingTerm degree frequency (amplitude degree) time) +
    diskForcingPrimitive degree frequency (amplitudeDerivative degree) time)) = _
  rw [Summable.tsum_add (linearSummable.add forceSummable) derivativeSummable,
    Summable.tsum_add linearSummable forceSummable, ← rate.map_tsum primitiveSummable]
  rfl

end

end EulerNonuniqueness.Paper
