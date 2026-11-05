import Mathlib

open MeasureTheory

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem integral_double_antiperiod_eq_zero {function : ℝ → Space} {halfPeriod : ℝ}
    (continuous : Continuous function) (antiperiodic : ∀ time, function (time + halfPeriod) = -function time) :
    (∫ time in (0 : ℝ)..(2 * halfPeriod), function time) = 0 := by
  have shifted : (∫ time in halfPeriod..(2 * halfPeriod), function time) =
      -(∫ time in (0 : ℝ)..halfPeriod, function time) := by
    calc
      _ = ∫ time in (0 : ℝ)..halfPeriod, function (time + halfPeriod) := by
        simpa only [zero_add, two_mul] using (intervalIntegral.integral_comp_add_right function halfPeriod
          (a := 0) (b := halfPeriod)).symm
      _ = ∫ time in (0 : ℝ)..halfPeriod, -function time :=
        intervalIntegral.integral_congr (fun time _ => antiperiodic time)
      _ = _ := intervalIntegral.integral_neg
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous.intervalIntegrable 0 halfPeriod) (continuous.intervalIntegrable halfPeriod (2 * halfPeriod)),
    shifted, add_neg_cancel]

end EulerNonuniqueness.General
