import EulerNonuniqueness.Section3.ContourCauchyTruncation

open MeasureTheory Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem banachContourCauchy_continuousOn_fixed_window (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {target : ℝ} (target_near : |target| ≤ Real.pi / 4) :
    ContinuousOn (contourCauchyKernel data.val.1 data.val.2.val.1 target)
      (Icc (-(5 * Real.pi / 4)) (5 * Real.pi / 4) \ {target}) := by
  have target_bounds := abs_le.mp target_near
  have chord_pos := sub_pos.mpr (small.trans_le (min_le_right _ _))
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

theorem banachContourCauchy_intervalIntegrable (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {target lower upper : ℝ} (target_near : |target| ≤ Real.pi / 4)
    (ordered : lower ≤ upper) (lower_bound : -(5 * Real.pi / 4) ≤ lower)
    (upper_bound : upper ≤ 5 * Real.pi / 4) (same_side : upper < target ∨ target < lower) :
    IntervalIntegrable (contourCauchyKernel data.val.1 data.val.2.val.1 target) volume lower upper := by
  apply ((banachContourCauchy_continuousOn_fixed_window data small target_near).mono ?_).intervalIntegrable
  rw [uIcc_of_le ordered]
  intro source membership
  refine ⟨⟨lower_bound.trans membership.1, membership.2.trans upper_bound⟩, ?_⟩
  simp only [mem_singleton_iff]
  rcases same_side with left | right
  · exact (membership.2.trans_lt left).ne
  · exact (right.trans_le membership.1).ne'

set_option maxHeartbeats 1000000 in
theorem banachContourCauchy_offCenter_far_bound (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {target : ℝ} (target_pos : 0 < target) (target_small : target ≤ Real.pi / 8) :
    ‖(∫ source in (-Real.pi)..(-2 * target), contourCauchyKernel data.val.1 data.val.2.val.1 target source) +
      ∫ source in (2 * target)..Real.pi, contourCauchyKernel data.val.1 data.val.2.val.1 target source‖ ≤
      (4 * ‖data‖ / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖)) * Real.sqrt Real.pi +
        2 * ‖data‖ / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖) := by
  let chord := 2 / (3 * Real.pi) - ‖data - standardCircleBanach‖
  have chord_pos : 0 < chord := sub_pos.mpr (small.trans_le (min_le_right _ _))
  have target_near : |target| ≤ Real.pi / 4 := by rw [abs_of_pos target_pos]; linarith [Real.pi_pos]
  have periodic : Function.Periodic (contourCauchyKernel data.val.1 data.val.2.val.1 target) (2 * Real.pi) := by
    intro source
    change data.val.2.val.1 (source + 2 * Real.pi) /
      (data.val.1 target - data.val.1 (source + 2 * Real.pi)) = _
    rw [PeriodicC1HolderHalf.periodic data source, PeriodicHolderHalf.periodic data.val.2 source]
    rfl
  have edge_integrable := banachContourCauchy_intervalIntegrable data small target_near
    (lower := -Real.pi) (upper := target - Real.pi)
    (by linarith) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inl (by linarith [Real.pi_pos]))
  have left_integrable := banachContourCauchy_intervalIntegrable data small target_near
    (lower := target - Real.pi) (upper := target - target)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inl (by linarith))
  have right_integrable := banachContourCauchy_intervalIntegrable data small target_near
    (lower := target + target) (upper := -Real.pi + 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inr (by linarith))
  have window := periodic_truncated_integral_window_eq periodic edge_integrable left_integrable right_integrable
  have centered := banachContourCauchy_truncated_integral_bound data small target target_pos
    (by linarith [Real.pi_pos] : target ≤ Real.pi)
  have fixed_bound :
      ‖(∫ source in (-Real.pi)..0, contourCauchyKernel data.val.1 data.val.2.val.1 target source) +
        ∫ source in (2 * target)..Real.pi, contourCauchyKernel data.val.1 data.val.2.val.1 target source‖ ≤
        (4 * ‖data‖ / chord) * Real.sqrt Real.pi := by
    have endpoint_first : -Real.pi + 2 * Real.pi = Real.pi := by ring
    have endpoint_second : target - Real.pi + 2 * Real.pi = target + Real.pi := by ring
    rw [sub_self, endpoint_first, endpoint_second, ← two_mul target] at window
    rw [window]
    simpa only [sub_self, ← two_mul, chord] using centered
  have strip_integrable := banachContourCauchy_intervalIntegrable data small target_near
    (lower := -2 * target) (upper := 0)
    (by linarith) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inl target_pos)
  have far_integrable := banachContourCauchy_intervalIntegrable data small target_near
    (lower := -Real.pi) (upper := -2 * target)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inl (by linarith))
  have strip_bound : ‖∫ source in (-2 * target)..0,
      contourCauchyKernel data.val.1 data.val.2.val.1 target source‖ ≤ 2 * ‖data‖ / chord := by
    have estimate := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -2 * target) (b := 0) (C := (‖data‖ / chord) / target)
      (f := contourCauchyKernel data.val.1 data.val.2.val.1 target) (fun source membership => by
        have source_mem : source ∈ Ioc (-2 * target) 0 := by
          simpa only [uIoc_of_le (by linarith : -2 * target ≤ 0)] using membership
        have distance : |target - source| = target - source := abs_of_pos (by linarith [source_mem.2])
        have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
          rw [abs_sub_comm source target, distance]
          linarith [source_mem.1, Real.pi_pos]
        have size := contourCauchyKernel_size (show target ≠ source by linarith [source_mem.2])
          (norm_nonneg data) chord_pos (PeriodicC1HolderHalf.speed_bound data source)
          (by simpa only [abs_sub_comm target source] using PeriodicC1HolderHalf.chord_bound_extended data nearby)
        exact size.trans (div_le_div_of_nonneg_left (by positivity) target_pos (by rw [distance]; linarith [source_mem.2])))
    have length : |(0 : ℝ) - -2 * target| = 2 * target := by rw [abs_of_pos (by linarith)]; ring
    rw [length] at estimate
    convert estimate using 1 <;> field_simp <;> ring
  have adjacent := intervalIntegral.integral_add_adjacent_intervals far_integrable strip_integrable
  have identity :
      (∫ source in (-Real.pi)..(-2 * target), contourCauchyKernel data.val.1 data.val.2.val.1 target source) +
        (∫ source in (2 * target)..Real.pi, contourCauchyKernel data.val.1 data.val.2.val.1 target source) =
      ((∫ source in (-Real.pi)..0, contourCauchyKernel data.val.1 data.val.2.val.1 target source) +
        ∫ source in (2 * target)..Real.pi, contourCauchyKernel data.val.1 data.val.2.val.1 target source) -
      ∫ source in (-2 * target)..0, contourCauchyKernel data.val.1 data.val.2.val.1 target source := by
    rw [← adjacent]
    abel
  rw [identity]
  exact (norm_sub_le _ _).trans (add_le_add fixed_bound strip_bound)

end EulerNonuniqueness.Paper
