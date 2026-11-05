import EulerNonuniqueness.Section3.RegularizedContourGreen
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

theorem regularizedContourLog_abs_le {scale radius : ℝ} (scale_positive : 0 < scale)
    (scale_le : scale ≤ 1) (radius_lower : 1 ≤ radius) (point position : ℂ)
    (nonzero : position ≠ point) (bounded : ‖position - point‖ ≤ radius) :
    |regularizedContourLog scale point position| ≤
      |Real.log ‖position - point‖| + (1 / 2 : ℝ) * Real.log (radius ^ 2 + 1) := by
  have distance_positive : 0 < ‖position - point‖ := norm_pos_iff.mpr (sub_ne_zero.mpr nonzero)
  have lower : Real.log ‖position - point‖ ≤ regularizedContourLog scale point position := by
    have monotone := Real.log_le_log (by positivity : 0 < ‖position - point‖ ^ 2)
      (le_add_of_nonneg_right (sq_nonneg scale))
    rw [Real.log_pow] at monotone
    norm_num only [Nat.cast_ofNat] at monotone
    unfold regularizedContourLog
    linarith
  have upper : regularizedContourLog scale point position ≤ (1 / 2 : ℝ) * Real.log (radius ^ 2 + 1) := by
    unfold regularizedContourLog
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.log_le_log (by positivity)
    nlinarith [sq_nonneg (radius - ‖position - point‖)]
  have constant_nonnegative : 0 ≤ (1 / 2 : ℝ) * Real.log (radius ^ 2 + 1) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [sq_nonneg radius]))
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log ‖position - point‖)],
    by linarith [abs_nonneg (Real.log ‖position - point‖)]⟩

theorem tendsto_regularizedContourLog {scales : ℕ → ℝ}
    (convergence : Tendsto scales atTop (𝓝 0)) (point position : ℂ) (nonzero : position ≠ point) :
    Tendsto (fun index => regularizedContourLog (scales index) point position) atTop
      (𝓝 (Real.log ‖position - point‖)) := by
  have squared_positive : 0 < ‖position - point‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr nonzero)) 2
  have denominator_convergence : Tendsto (fun index => ‖position - point‖ ^ 2 + scales index ^ 2)
      atTop (𝓝 (‖position - point‖ ^ 2)) := by
    simpa using tendsto_const_nhds.add (convergence.pow 2)
  have log_convergence := (Real.continuousAt_log squared_positive.ne').tendsto.comp denominator_convergence
  have scaled := log_convergence.const_mul (1 / 2 : ℝ)
  simpa only [regularizedContourLog, Real.log_pow, Nat.cast_ofNat, one_div, inv_mul_cancel_left₀ (by norm_num : (2 : ℝ) ≠ 0)] using scaled

theorem tendsto_intervalIntegral_regularizedContourLog
    {scales : ℕ → ℝ} (positive : ∀ index, 0 < scales index)
    (scales_le : ∀ index, scales index ≤ 1) (convergence : Tendsto scales atTop (𝓝 0))
    (curve tangent : ℝ → ℂ) (point : ℂ) (lower upper radius : ℝ)
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (radius_lower : 1 ≤ radius) (bounded : ∀ label ∈ uIcc lower upper, ‖curve label - point‖ ≤ radius)
    (nonzero : ∀ᵐ label ∂(volume.restrict (uIoc lower upper)), curve label ≠ point)
    (log_integrable : IntervalIntegrable (fun label => Real.log ‖curve label - point‖ • tangent label)
      volume lower upper) :
    Tendsto (fun index => ∫ label in lower..upper,
      regularizedContourLog (scales index) point (curve label) • tangent label) atTop
      (𝓝 (∫ label in lower..upper, Real.log ‖curve label - point‖ • tangent label)) := by
  let bound : ℝ → ℝ := fun label => ‖Real.log ‖curve label - point‖ • tangent label‖ +
    ((1 / 2 : ℝ) * Real.log (radius ^ 2 + 1)) * ‖tangent label‖
  have bound_integrable : Integrable bound (volume.restrict (uIoc lower upper)) :=
    (intervalIntegrable_iff.mp log_integrable).norm.add
      (((tangent_continuous.intervalIntegrable lower upper).def').norm.const_mul _)
  have dominated : Tendsto (fun index => ∫ label in uIoc lower upper,
      regularizedContourLog (scales index) point (curve label) • tangent label) atTop
      (𝓝 (∫ label in uIoc lower upper, Real.log ‖curve label - point‖ • tangent label)) := by
    apply tendsto_integral_of_dominated_convergence bound
    · intro index
      exact (((regularizedContourLog_continuous (positive index) point).comp curve_continuous).smul
        tangent_continuous).aestronglyMeasurable
    · exact bound_integrable
    · intro index
      filter_upwards [nonzero, ae_restrict_mem measurableSet_uIoc] with label label_nonzero label_mem
      have scalar_bound := regularizedContourLog_abs_le (positive index) (scales_le index) radius_lower
        point (curve label) label_nonzero (bounded label ⟨label_mem.1.le, label_mem.2⟩)
      dsimp only [bound]
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      nlinarith [mul_le_mul_of_nonneg_right scalar_bound (norm_nonneg (tangent label))]
    · filter_upwards [nonzero] with label label_nonzero
      exact (tendsto_regularizedContourLog convergence point (curve label) label_nonzero).smul tendsto_const_nhds
  simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc] using
    dominated.const_smul (if lower ≤ upper then (1 : ℝ) else -1)

end

end EulerNonuniqueness.Paper
