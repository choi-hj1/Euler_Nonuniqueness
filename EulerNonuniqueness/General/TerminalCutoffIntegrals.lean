import EulerNonuniqueness.General.TerminalCutoff

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem integral_deriv_terminalCutoff {horizon : ℝ} (positive : 0 < horizon) (index : ℕ) :
    (∫ time in Ioo 0 horizon, deriv (terminalCutoff horizon index) time) = -1 := by
  have smooth := contDiff_terminalCutoff horizon index
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time _ => (smooth.differentiable (by simp) time).hasDerivAt)
    ((smooth.continuous_deriv (by simp)).intervalIntegrable 0 horizon)
  rw [intervalIntegral.integral_of_le positive.le, integral_Ioc_eq_integral_Ioo,
    terminalCutoff_eq_zero_after positive index le_rfl, terminalCutoff_at_zero positive index] at identity
  simpa only [zero_sub] using identity

theorem integral_norm_deriv_terminalCutoff_le {horizon : ℝ} (positive : 0 < horizon)
    {bound : ℝ} (bounded : ∀ position, ‖deriv Real.smoothTransition position‖ ≤ bound)
    (index : ℕ) : (∫ time in Ioo 0 horizon, ‖deriv (terminalCutoff horizon index) time‖) ≤ bound := by
  let window := Icc (horizon - horizon / ((index : ℝ) + 1)) horizon
  have supportBound : Function.support (fun time => ‖deriv (terminalCutoff horizon index) time‖) ⊆ window := by
    intro time nonzero
    apply support_deriv_terminalCutoff positive index
    intro zero
    exact nonzero (by change ‖deriv (terminalCutoff horizon index) time‖ = 0; rw [zero, norm_zero])
  have compact : HasCompactSupport (fun time => ‖deriv (terminalCutoff horizon index) time‖) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc supportBound
  have continuous := (contDiff_terminalCutoff horizon index).continuous_deriv (by simp)
  have integrable : Integrable (fun time => ‖deriv (terminalCutoff horizon index) time‖) :=
    continuous.norm.integrable_of_hasCompactSupport compact
  have indicatorEquality := indicator_eq_self.mpr supportBound
  have constantIntegrable : IntegrableOn (fun _ : ℝ => (((index : ℝ) + 1) / horizon) * bound) window :=
    integrableOn_const.mpr (Or.inr isCompact_Icc.measure_lt_top)
  calc
    _ ≤ ∫ time, ‖deriv (terminalCutoff horizon index) time‖ :=
      setIntegral_le_integral integrable (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ = ∫ time in window, ‖deriv (terminalCutoff horizon index) time‖ := by
      rw [← integral_indicator measurableSet_Icc, indicatorEquality]
    _ ≤ ∫ _time in window, (((index : ℝ) + 1) / horizon) * bound :=
      integral_mono_ae integrable.integrableOn constantIntegrable
        (Filter.Eventually.of_forall fun time => norm_deriv_terminalCutoff_le positive bounded index time)
    _ = bound := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le (sub_le_self _ (by positivity))]
      simp only [smul_eq_mul]
      have indexNonzero : (index : ℝ) + 1 ≠ 0 := by positivity
      field_simp [positive.ne', indexNonzero]
      ring

end EulerNonuniqueness
