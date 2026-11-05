import EulerNonuniqueness.Section3.DiskForcingSeriesDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

open Set

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance forcingWeightedDerivativeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem natural_square_le_geometric (degree : ℕ) :
    (degree : ℝ) ^ 2 ≤ 4 * (2 : ℝ) ^ degree := by
  induction degree with
  | zero => norm_num
  | succ degree induction =>
    by_cases small : degree ≤ 2
    · interval_cases degree <;> norm_num
    · have large : (3 : ℝ) ≤ degree := by exact_mod_cast (by omega : 3 ≤ degree)
      calc
        ((degree + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * (degree : ℝ) ^ 2 := by push_cast; nlinarith
        _ ≤ 2 * (4 * (2 : ℝ) ^ degree) := mul_le_mul_of_nonneg_left induction (by norm_num)
        _ = _ := by rw [pow_succ]; ring

theorem diskCircleMode_geometric_norm_bound (degree : ℕ) :
    ‖c1Conjugate (diskCircleMode (degree + 1))‖ ≤ 8 * (2 : ℝ) ^ (degree + 1) := by
  exact ((c1Conjugate_norm_bound _).trans (diskCircleMode_norm_bound degree)).trans
    (by nlinarith [natural_square_le_geometric (degree + 1)])

theorem diskForcingPrimitive_tsum_hasDerivAt_of_weighted_bounds {frequency left right initial time : ℝ}
    (nonzero : frequency ≠ 0) (amplitude amplitudeDerivative : ℕ → ℝ → ℂ)
    (amplitudeBound derivativeBound : ℕ → ℝ)
    (amplitudeEquation : ∀ degree current, current ∈ Ioo left right →
      HasDerivAt (amplitude degree) (amplitudeDerivative degree current) current)
    (bounds : ∀ degree current, current ∈ Ioo left right →
      ‖amplitude degree current‖ ≤ amplitudeBound degree ∧
        ‖amplitudeDerivative degree current‖ ≤ derivativeBound degree)
    (summableAmplitude : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * amplitudeBound degree))
    (summableDerivative : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * derivativeBound degree))
    (initialMember : initial ∈ Ioo left right) (member : time ∈ Ioo left right) :
    HasDerivAt (fun current => ∑' degree, diskForcingPrimitive degree frequency (amplitude degree) current)
      (∑' degree, diskForcingPrimitiveJet degree frequency (amplitude degree) (amplitudeDerivative degree) time) time := by
  have transfer (envelope : ℕ → ℝ) (nonnegative : ∀ degree, 0 ≤ envelope degree)
      (summable : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * envelope degree)) :
      Summable (fun degree => ‖c1Conjugate (diskCircleMode (degree + 1))‖ * envelope degree) := by
    apply Summable.of_nonneg_of_le (fun degree => mul_nonneg (norm_nonneg _) (nonnegative degree))
      (fun degree => ?_) (summable.mul_left 8)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (diskCircleMode_geometric_norm_bound degree) (nonnegative degree)
  exact diskForcingPrimitive_tsum_hasDerivAt nonzero amplitude amplitudeDerivative amplitudeBound derivativeBound
    amplitudeEquation bounds
    (transfer amplitudeBound (fun degree => (norm_nonneg _).trans (bounds degree initial initialMember).1) summableAmplitude)
    (transfer derivativeBound (fun degree => (norm_nonneg _).trans (bounds degree initial initialMember).2) summableDerivative)
    initialMember member

end

end EulerNonuniqueness.Paper
