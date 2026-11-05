import Mathlib

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

theorem tendsto_log_exp_profile_sub {function : ℝ → ℝ} {filter : Filter ℝ} {rate : ℝ}
    (rateNonzero : rate ≠ 0)
    (normalized : Tendsto (fun time => Real.exp (-rate * time) * function time) filter (𝓝 1)) :
    Tendsto (fun time => Real.log (function time) / rate - time) filter (𝓝 0) := by
  have logarithmic := ((Real.continuousAt_log one_ne_zero).tendsto.comp normalized).div_const rate
  simp only [Real.log_one, zero_div] at logarithmic
  apply logarithmic.congr'
  filter_upwards [normalized.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))] with time positive
  have functionPositive : 0 < function time := by
    exact (mul_pos_iff.mp positive).resolve_right (by
      intro negative
      exact (not_lt_of_gt (Real.exp_pos _)) negative.1) |>.2
  dsimp only [Function.comp_apply]
  rw [Real.log_mul (Real.exp_ne_zero _) functionPositive.ne', Real.log_exp]
  field_simp
  ring

end EulerNonuniqueness.General
