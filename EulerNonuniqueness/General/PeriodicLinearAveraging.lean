import Mathlib

open MeasureTheory

namespace EulerNonuniqueness.General

noncomputable section

variable {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]

theorem periodic_linear_weighted_average_identity
    (operator : Value →L[ℝ] Value) {trajectory : ℝ → Value} {period : ℝ}
    (periodNonzero : period ≠ 0)
    (actual : ∀ time, HasDerivAt trajectory (operator (trajectory time)) time)
    (endpoint : trajectory period = trajectory 0) :
    operator ((1 / period : ℝ) • ∫ time in (0 : ℝ)..period, time • trajectory time) =
      trajectory 0 - (1 / period : ℝ) • ∫ time in (0 : ℝ)..period, trajectory time := by
  have continuous : Continuous trajectory := continuous_iff_continuousAt.mpr (fun time => (actual time).continuousAt)
  have sourceContinuous : Continuous (fun time => operator (trajectory time)) := operator.continuous.comp continuous
  have derivative (time : ℝ) : HasDerivAt (fun current => current • trajectory current)
      (trajectory time + time • operator (trajectory time)) time := by
    simpa only [one_smul, id_eq, add_comm] using (hasDerivAt_id time).smul (actual time)
  have trajectoryIntegrable := continuous.intervalIntegrable (μ := volume) 0 period
  have weightedIntegrable : IntervalIntegrable (fun time : ℝ => time • trajectory time) volume 0 period := by
    simpa only [id_eq] using (continuous_id.smul continuous).intervalIntegrable (μ := volume) 0 period
  have weightedSourceIntegrable : IntervalIntegrable (fun time : ℝ => time • operator (trajectory time)) volume 0 period := by
    simpa only [id_eq] using (continuous_id.smul sourceContinuous).intervalIntegrable (μ := volume) 0 period
  have sourceIntegrable : IntervalIntegrable
      (fun time : ℝ => trajectory time + time • operator (trajectory time)) volume 0 period := by
    simpa only [id_eq] using
      (continuous.add (continuous_id.smul sourceContinuous)).intervalIntegrable (μ := volume) 0 period
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => derivative time)
    sourceIntegrable
  rw [intervalIntegral.integral_add trajectoryIntegrable weightedSourceIntegrable, endpoint,
    zero_smul, sub_zero] at identity
  have rearranged : (∫ time in (0 : ℝ)..period, time • operator (trajectory time)) =
      period • trajectory 0 - ∫ time in (0 : ℝ)..period, trajectory time :=
    eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using identity)
  have commutes := operator.intervalIntegral_comp_comm weightedIntegrable
  simp only [map_smul] at commutes
  rw [map_smul, ← commutes, rearranged, smul_sub, smul_smul,
    one_div_mul_cancel periodNonzero, one_smul]

theorem periodic_linear_average_kernel
    (operator : Value →L[ℝ] Value) {trajectory : ℝ → Value} {period : ℝ}
    (actual : ∀ time, HasDerivAt trajectory (operator (trajectory time)) time)
    (endpoint : trajectory period = trajectory 0) :
    operator ((1 / period : ℝ) • ∫ time in (0 : ℝ)..period, trajectory time) = 0 := by
  have continuous : Continuous trajectory := continuous_iff_continuousAt.mpr (fun time => (actual time).continuousAt)
  have integrable := continuous.intervalIntegrable (μ := volume) 0 period
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => actual time)
    ((operator.continuous.comp continuous).intervalIntegrable (μ := volume) 0 period)
  rw [endpoint, sub_self, operator.intervalIntegral_comp_comm integrable] at identity
  rw [map_smul, identity, smul_zero]

end

end EulerNonuniqueness.General
