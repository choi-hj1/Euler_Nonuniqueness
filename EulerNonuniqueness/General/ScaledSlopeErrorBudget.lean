import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem scaled_slope_error_budget {slopeConstant errorConstant self error forcing : ℝ}
    (slopeNonnegative : 0 ≤ slopeConstant) (errorOne : 1 ≤ errorConstant)
    (selfNonnegative : 0 ≤ self) (bound : error ≤ errorConstant * forcing) :
    slopeConstant * (self + error) ≤ (slopeConstant * errorConstant) * (self + forcing) := by
  have selfBound : self ≤ errorConstant * self := by nlinarith
  have total := add_le_add selfBound bound
  have scaled := mul_le_mul_of_nonneg_left total slopeNonnegative
  convert scaled using 1 <;> ring

end EulerNonuniqueness.General
