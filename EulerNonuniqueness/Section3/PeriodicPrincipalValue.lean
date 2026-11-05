import EulerNonuniqueness.Section3.ContourBanachVelocity

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

theorem periodic_truncated_integral_window_eq {kernel : ℝ → ℂ}
    {period first second target cutoff : ℝ} (periodic : Function.Periodic kernel period)
    (edge_integrable : IntervalIntegrable kernel volume first second)
    (left_integrable : IntervalIntegrable kernel volume second (target - cutoff))
    (right_integrable : IntervalIntegrable kernel volume (target + cutoff) (first + period)) :
    (∫ source in first..(target - cutoff), kernel source) +
      (∫ source in (target + cutoff)..(first + period), kernel source) =
    (∫ source in second..(target - cutoff), kernel source) +
      ∫ source in (target + cutoff)..(second + period), kernel source := by
  have negative_period : ∀ source : ℝ, kernel (source - period) = kernel source := by
    intro source
    simpa only [sub_add_cancel] using (periodic (source - period)).symm
  have shifted_integrable : IntervalIntegrable kernel volume (first + period) (second + period) := by
    simpa only [negative_period] using edge_integrable.comp_sub_right period
  have shifted_integral : (∫ source in (first + period)..(second + period), kernel source) =
      ∫ source in first..second, kernel source := by
    have identity : (fun source => kernel (source + period)) = kernel := funext periodic
    calc
      _ = ∫ source in first..second, kernel (source + period) :=
        (intervalIntegral.integral_comp_add_right kernel period).symm
      _ = _ := by rw [identity]
  have left := intervalIntegral.integral_add_adjacent_intervals edge_integrable left_integrable
  have right := intervalIntegral.integral_add_adjacent_intervals right_integrable shifted_integrable
  rw [shifted_integral] at right
  rw [← left, ← right]
  ring

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem banachContourCauchy_principal_value_fixed_window (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {target : ℝ} (target_near : |target| ≤ Real.pi / 4) :
    Tendsto (fun cutoff : ℝ =>
      (∫ source in (-Real.pi)..(target - cutoff), contourCauchyKernel data.val.1 data.val.2.val.1 target source) +
        ∫ source in (target + cutoff)..Real.pi, contourCauchyKernel data.val.1 data.val.2.val.1 target source)
      (𝓝[>] 0) (𝓝 (-(Real.pi : ℂ) * Complex.I)) := by
  have target_bounds := abs_le.mp target_near
  have chord_pos : 0 < 2 / (3 * Real.pi) - ‖data - standardCircleBanach‖ :=
    sub_pos.mpr (small.trans_le (min_le_right _ _))
  have coefficient_le : 2 / (3 * Real.pi) ≤ 2 / Real.pi := by
    have positive : 0 < 2 / Real.pi := by positivity
    have identity : 2 / (3 * Real.pi) = (2 / Real.pi) / 3 := by ring
    rw [identity]
    linarith
  have periodic : Function.Periodic (contourCauchyKernel data.val.1 data.val.2.val.1 target) (2 * Real.pi) := by
    intro source
    change data.val.2.val.1 (source + 2 * Real.pi) /
      (data.val.1 target - data.val.1 (source + 2 * Real.pi)) = _
    rw [PeriodicC1HolderHalf.periodic data source, PeriodicHolderHalf.periodic data.val.2 source]
    rfl
  have continuous : ContinuousOn (contourCauchyKernel data.val.1 data.val.2.val.1 target)
      (Icc (-(5 * Real.pi / 4)) (5 * Real.pi / 4) \ {target}) := by
    apply data.val.2.val.1.continuous.continuousOn.div
      (continuousOn_const.sub data.val.1.continuous.continuousOn)
    intro source membership
    have distinct : target ≠ source := Ne.symm (by simpa only [mem_singleton_iff] using membership.2)
    have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
      rw [abs_le]
      constructor <;> linarith [membership.1.1, membership.1.2, target_bounds.1, target_bounds.2]
    exact norm_ne_zero_iff.mp (ne_of_gt ((mul_pos chord_pos (abs_pos.mpr
      (sub_ne_zero.mpr distinct))).trans_le
        (by simpa only [abs_sub_comm target source] using PeriodicC1HolderHalf.chord_bound_extended data nearby)))
  have limit := contourCauchy_near_circle_principal_value_at
    (norm_nonneg data) (norm_nonneg (data - standardCircleBanach))
    ((small.trans_le (min_le_right _ _)).trans_le coefficient_le)
    data.val.1.continuous data.val.2.val.1.continuous
    (PeriodicC1HolderHalf.hasDerivAt data) (PeriodicC1HolderHalf.derivative_holder_bound data)
    (PeriodicC1HolderHalf.derivative_close_circle data) (PeriodicC1HolderHalf.periodic data) target
  apply limit.congr'
  filter_upwards [Ioo_mem_nhdsGT (by positivity : 0 < Real.pi / 2)] with cutoff cutoff_mem
  have edge_integrable : IntervalIntegrable (contourCauchyKernel data.val.1 data.val.2.val.1 target)
      volume (-Real.pi) (target - Real.pi) := by
    apply (continuous.mono ?_).intervalIntegrable
    intro source membership
    rcases mem_uIcc.mp membership with membership | membership
    all_goals
      refine ⟨⟨by linarith [membership.1, target_bounds.1, Real.pi_pos],
        by linarith [membership.2, target_bounds.2, Real.pi_pos]⟩, ?_⟩
      simp only [mem_singleton_iff]
      intro equal
      subst source
      linarith [membership.2, target_bounds.1, Real.pi_pos]
  have left_integrable : IntervalIntegrable (contourCauchyKernel data.val.1 data.val.2.val.1 target)
      volume (target - Real.pi) (target - cutoff) := by
    apply (continuous.mono ?_).intervalIntegrable
    rw [uIcc_of_le (by linarith [cutoff_mem.2] : target - Real.pi ≤ target - cutoff)]
    intro source membership
    refine ⟨⟨by linarith [membership.1, target_bounds.1],
      by linarith [membership.2, target_bounds.2, cutoff_mem.1, Real.pi_pos]⟩, ?_⟩
    simp only [mem_singleton_iff]
    linarith [membership.2, cutoff_mem.1]
  have right_integrable : IntervalIntegrable (contourCauchyKernel data.val.1 data.val.2.val.1 target)
      volume (target + cutoff) (-Real.pi + 2 * Real.pi) := by
    apply (continuous.mono ?_).intervalIntegrable
    rw [uIcc_of_le (by linarith [cutoff_mem.2, target_bounds.2, Real.pi_pos] :
      target + cutoff ≤ -Real.pi + 2 * Real.pi)]
    intro source membership
    refine ⟨⟨by linarith [membership.1, target_bounds.1, cutoff_mem.1, Real.pi_pos],
      by linarith [membership.2, Real.pi_pos]⟩, ?_⟩
    simp only [mem_singleton_iff]
    linarith [membership.1, cutoff_mem.1]
  have identity := periodic_truncated_integral_window_eq periodic edge_integrable left_integrable right_integrable
  convert identity.symm using 1 <;> congr 1 <;> congr 1 <;> ring

end EulerNonuniqueness.Paper
