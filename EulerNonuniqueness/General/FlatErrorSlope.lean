import EulerNonuniqueness.General.ScaledErrorSlope

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

theorem eventually_slope_lt_of_flat_scaled_error
    {curve : ℝ → ℝ} {time slopeConstant errorConstant self error first second third : ℝ}
    (slopeNonnegative : 0 ≤ slopeConstant) (errorOne : 1 ≤ errorConstant)
    (selfNonnegative : 0 ≤ self) (bound : error ≤ errorConstant * (first + second + third))
    (slopes : ∀ threshold, slopeConstant * (self + error) < threshold →
      ∀ᶠ later in 𝓝[>] time, slope curve time later < threshold) :
    ∀ threshold, (slopeConstant * errorConstant) * (self + first + second + third) < threshold →
      ∀ᶠ later in 𝓝[>] time, slope curve time later < threshold := by
  have actual := eventually_slope_lt_of_scaled_error slopeNonnegative errorOne selfNonnegative bound slopes
  intro threshold strict
  apply actual threshold
  simpa only [add_assoc] using strict

end EulerNonuniqueness.General
