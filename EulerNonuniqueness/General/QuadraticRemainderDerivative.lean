import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace EulerNonuniqueness.General

open Filter
open scoped Topology

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem hasFDerivAt_of_eventual_quadratic_remainder
    (function : Domain → Range) (linear : Domain →L[ℝ] Range) (base : Domain)
    {constant : ℝ} (constantNonnegative : 0 ≤ constant)
    (remainder : ∀ᶠ increment in 𝓝 (0 : Domain),
      ‖function (base + increment) - function base - linear increment‖ ≤ constant * ‖increment‖ ^ 2) :
    HasFDerivAt function linear base := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro epsilon positive
  have denominatorPositive : 0 < constant + 1 := by linarith
  have small : ∀ᶠ increment in 𝓝 (0 : Domain), ‖increment‖ < epsilon / (constant + 1) := by
    exact (continuous_norm.tendsto (0 : Domain)).eventually
      (by simpa only [norm_zero] using eventually_lt_nhds (div_pos positive denominatorPositive))
  filter_upwards [remainder, small] with increment bound tiny
  have productSmall : (constant + 1) * ‖increment‖ ≤ epsilon := by
    have actual := (lt_div_iff₀ denominatorPositive).mp tiny
    nlinarith
  calc
    _ ≤ constant * ‖increment‖ ^ 2 := bound
    _ ≤ ((constant + 1) * ‖increment‖) * ‖increment‖ := by nlinarith [sq_nonneg ‖increment‖]
    _ ≤ epsilon * ‖increment‖ := mul_le_mul_of_nonneg_right productSmall (norm_nonneg _)

end EulerNonuniqueness.General
