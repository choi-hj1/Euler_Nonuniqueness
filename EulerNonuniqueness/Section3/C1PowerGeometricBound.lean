import EulerNonuniqueness.Section3.RelabeledDiskForcingPrimitive

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem c1NaturalPower_geometric_norm_bound (data : PeriodicC1HolderHalf) (degree : ℕ) :
    ‖c1NaturalPower data degree‖ ≤ (8 * ‖data‖) ^ degree := by
  induction degree with
  | zero =>
      simpa only [c1NaturalPower, pow_zero, norm_one] using c1Constant_norm_bound (1 : ℂ)
  | succ degree induction =>
      calc
        _ ≤ 8 * ‖data‖ * ‖c1NaturalPower data degree‖ := c1Product_norm_bound _ _
        _ ≤ 8 * ‖data‖ * (8 * ‖data‖) ^ degree := mul_le_mul_of_nonneg_left induction (by positivity)
        _ = _ := by rw [pow_succ]; ring

theorem c1NaturalPower_norm_bound_twentyFour (data : PeriodicC1HolderHalf)
    (bound : ‖data‖ ≤ 3) (degree : ℕ) :
    ‖c1NaturalPower data degree‖ ≤ (24 : ℝ) ^ degree := by
  refine (c1NaturalPower_geometric_norm_bound data degree).trans ?_
  exact pow_le_pow_left₀ (by positivity) (by linarith) degree

end

end EulerNonuniqueness.Paper
