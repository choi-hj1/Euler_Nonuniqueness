import EulerNonuniqueness.General.ScaledSlopeErrorBudget
import Mathlib.Analysis.Calculus.Deriv.Slope

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

theorem eventually_slope_lt_of_scaled_error
    {curve : ℝ → ℝ} {time slopeConstant errorConstant self error forcing : ℝ}
    (slopeNonnegative : 0 ≤ slopeConstant) (errorOne : 1 ≤ errorConstant)
    (selfNonnegative : 0 ≤ self) (bound : error ≤ errorConstant * forcing)
    (slopes : ∀ threshold, slopeConstant * (self + error) < threshold →
      ∀ᶠ later in 𝓝[>] time, slope curve time later < threshold) :
    ∀ threshold, (slopeConstant * errorConstant) * (self + forcing) < threshold →
      ∀ᶠ later in 𝓝[>] time, slope curve time later < threshold := by
  intro threshold strict
  exact slopes threshold ((scaled_slope_error_budget slopeNonnegative errorOne selfNonnegative bound).trans_lt strict)

end EulerNonuniqueness.General
