import EulerNonuniqueness.Section3.HolderBanachModel

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem PeriodicHolderHalf.norm_le_of_bounds (data : PeriodicHolderHalf) {bound : ℝ}
    (bound_nonneg : 0 ≤ bound) (value_bound : ∀ label : ℝ, ‖data.val.1 label‖ ≤ bound)
    (holder_bound : ∀ first second : ℝ,
      ‖data.val.1 first - data.val.1 second‖ ≤ bound * Real.sqrt |first - second|) :
    ‖data‖ ≤ bound := by
  change max ‖data.val.1‖ ‖data.val.2‖ ≤ bound
  apply max_le
  · exact (BoundedContinuousFunction.norm_le bound_nonneg).mpr value_bound
  · apply (BoundedContinuousFunction.norm_le bound_nonneg).mpr
    intro pair
    have root_pos := Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr pair.property))
    have identity := congrArg norm (data.property.1 pair)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos root_pos] at identity
    have estimate := holder_bound pair.val.1 pair.val.2
    rw [← identity, mul_comm bound] at estimate
    exact (mul_le_mul_left root_pos).mp estimate

end EulerNonuniqueness.Paper
