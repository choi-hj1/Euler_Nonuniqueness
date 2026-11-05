import EulerNonuniqueness.General.WeightedIntegralAbsorption

open MeasureTheory Set

namespace EulerNonuniqueness

theorem integral_forward_decay {rate first last : ℝ} (ratePositive : 0 < rate) :
    (∫ current in first..last, Real.exp (-rate * (last - current))) =
      (1 - Real.exp (-rate * (last - first))) / rate := by
  have derivative (time : ℝ) :
      HasDerivAt (fun current => Real.exp (-rate * (last - current)) / rate)
        (Real.exp (-rate * (last - time))) time := by
    have exponent : HasDerivAt (fun current : ℝ => -rate * (last - current)) rate time := by
      convert ((hasDerivAt_id time).const_sub last).const_mul (-rate) using 1 <;> ring
    convert exponent.exp.div_const rate using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => derivative time)
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring

theorem integral_backward_decay {rate first last : ℝ} (ratePositive : 0 < rate) :
    (∫ current in first..last, Real.exp (-rate * (current - first))) =
      (1 - Real.exp (-rate * (last - first))) / rate := by
  have derivative (time : ℝ) :
      HasDerivAt (fun current => -Real.exp (-rate * (current - first)) / rate)
        (Real.exp (-rate * (time - first))) time := by
    have exponent : HasDerivAt (fun current : ℝ => -rate * (current - first)) (-rate) time := by
      simpa only [mul_one] using ((hasDerivAt_id time).sub_const first).const_mul (-rate)
    convert exponent.exp.neg.div_const rate using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => derivative time)
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring

theorem integral_twoSided_decay_le {rate horizon time : ℝ}
    (ratePositive : 0 < rate) (inside : time ∈ Icc 0 horizon) :
    (∫ current in (0 : ℝ)..horizon, Real.exp (-rate * |time - current|)) ≤ 2 / rate := by
  have continuous : Continuous (fun current : ℝ => Real.exp (-rate * |time - current|)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id).abs)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous.intervalIntegrable 0 time) (continuous.intervalIntegrable time horizon)]
  have firstIdentity : (∫ current in (0 : ℝ)..time, Real.exp (-rate * |time - current|)) =
      (1 - Real.exp (-rate * time)) / rate := by
    calc
      _ = ∫ current in (0 : ℝ)..time, Real.exp (-rate * (time - current)) := by
        apply intervalIntegral.integral_congr
        intro current membership
        have membership' : current ∈ Icc 0 time := by simpa only [uIcc_of_le inside.1] using membership
        dsimp only
        rw [abs_of_nonneg (sub_nonneg.mpr membership'.2)]
      _ = _ := by simpa only [sub_zero] using integral_forward_decay (first := 0) (last := time) ratePositive
  have secondIdentity : (∫ current in time..horizon, Real.exp (-rate * |time - current|)) =
      (1 - Real.exp (-rate * (horizon - time))) / rate := by
    calc
      _ = ∫ current in time..horizon, Real.exp (-rate * (current - time)) := by
        apply intervalIntegral.integral_congr
        intro current membership
        have membership' : current ∈ Icc time horizon := by simpa only [uIcc_of_le inside.2] using membership
        dsimp only
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr membership'.1)]
      _ = _ := integral_backward_decay ratePositive
  rw [firstIdentity, secondIdentity]
  have firstPositive := Real.exp_pos (-rate * time)
  have secondPositive := Real.exp_pos (-rate * (horizon - time))
  calc
    _ ≤ 1 / rate + 1 / rate := add_le_add
      (div_le_div_of_nonneg_right (by linarith [firstPositive]) ratePositive.le)
      (div_le_div_of_nonneg_right (by linarith [secondPositive]) ratePositive.le)
    _ = _ := by ring

end EulerNonuniqueness
