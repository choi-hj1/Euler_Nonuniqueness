import EulerNonuniqueness.Section3.ContourKernelTruncationParameter

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem contourCauchyKernel_normalized_shift (offset : ℝ) (data : PeriodicC1HolderHalf) (target source : ℝ) :
    contourCauchyKernel (normalizedContourShift offset data).val.1
      (normalizedContourShift offset data).val.2.val.1 target source =
      contourCauchyKernel data.val.1 data.val.2.val.1 (target + offset) (source + offset) := by
  have rotation_ne : (standardCircle offset)⁻¹ ≠ 0 := by simp [standardCircle, Complex.exp_ne_zero]
  unfold contourCauchyKernel
  rw [normalizedContourShift_value, normalizedContourShift_value, normalizedContourShift_tangent,
    ← mul_sub, mul_div_mul_left _ _ rotation_ne]

set_option maxHeartbeats 1000000 in
theorem contourCauchyKernel_parameter_truncated_bound (first second : PeriodicC1HolderHalf)
    {radius cutoff : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius)
    (target : ℝ) (cutoff_pos : 0 < cutoff) (cutoff_le : cutoff ≤ Real.pi) :
    ‖(∫ source in (target - Real.pi)..(target - cutoff),
        contourCauchyKernel first.val.1 first.val.2.val.1 target source -
          contourCauchyKernel second.val.1 second.val.2.val.1 target source) +
      ∫ source in (target + cutoff)..(target + Real.pi),
        contourCauchyKernel first.val.1 first.val.2.val.1 target source -
          contourCauchyKernel second.val.1 second.val.2.val.1 target source‖ ≤
      4 * ‖first - second‖ * (1 / (2 / (3 * Real.pi) - radius) +
        (radius + 2) / (2 / (3 * Real.pi) - radius) ^ 2) * Real.sqrt Real.pi := by
  have actual := contourCauchyKernel_parameter_truncated_zero_bound
    (normalizedContourShift target first) (normalizedContourShift target second) radius_nonneg radius_small
    (by rwa [normalizedContourShift_distance_circle]) (by rwa [normalizedContourShift_distance_circle]) cutoff_pos cutoff_le
  rw [← normalizedContourShift_sub, normalizedContourShift_norm] at actual
  simp_rw [contourCauchyKernel_normalized_shift, zero_add] at actual
  have left_shift := intervalIntegral.integral_comp_add_right
    (fun source => contourCauchyKernel first.val.1 first.val.2.val.1 target source -
      contourCauchyKernel second.val.1 second.val.2.val.1 target source) target
    (a := -Real.pi) (b := -cutoff)
  have right_shift := intervalIntegral.integral_comp_add_right
    (fun source => contourCauchyKernel first.val.1 first.val.2.val.1 target source -
      contourCauchyKernel second.val.1 second.val.2.val.1 target source) target
    (a := cutoff) (b := Real.pi)
  rw [left_shift, right_shift] at actual
  convert actual using 1 <;> congr 1 <;> congr 1 <;> congr 1 <;> ring

set_option maxHeartbeats 1000000 in
theorem contourCauchyKernel_parameter_offCenter_far_bound (first second : PeriodicC1HolderHalf)
    {radius target : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius)
    (target_pos : 0 < target) (target_small : target ≤ Real.pi / 8) :
    ‖(∫ source in (-Real.pi)..(-2 * target),
        contourCauchyKernel first.val.1 first.val.2.val.1 target source -
          contourCauchyKernel second.val.1 second.val.2.val.1 target source) +
      ∫ source in (2 * target)..Real.pi,
        contourCauchyKernel first.val.1 first.val.2.val.1 target source -
          contourCauchyKernel second.val.1 second.val.2.val.1 target source‖ ≤
      ‖first - second‖ * (1 / (2 / (3 * Real.pi) - radius) +
        (radius + 2) / (2 / (3 * Real.pi) - radius) ^ 2) * (4 * Real.sqrt Real.pi + 2) := by
  let kernel := fun source => contourCauchyKernel first.val.1 first.val.2.val.1 target source -
    contourCauchyKernel second.val.1 second.val.2.val.1 target source
  let chord := 2 / (3 * Real.pi) - radius
  let constant := ‖first - second‖ * (1 / chord + (radius + 2) / chord ^ 2)
  have chord_pos : 0 < chord := sub_pos.mpr (radius_small.trans_le (min_le_right _ _))
  have constant_nonneg : 0 ≤ constant := by dsimp only [constant]; positivity
  have target_near : |target| ≤ Real.pi / 4 := by rw [abs_of_pos target_pos]; linarith [Real.pi_pos]
  have periodic : Function.Periodic kernel (2 * Real.pi) := by
    intro source
    unfold kernel contourCauchyKernel
    rw [PeriodicC1HolderHalf.periodic first source, PeriodicHolderHalf.periodic first.val.2 source,
      PeriodicC1HolderHalf.periodic second source, PeriodicHolderHalf.periodic second.val.2 source]
  have integrable : ∀ lower upper : ℝ, lower ≤ upper → -(5 * Real.pi / 4) ≤ lower →
      upper ≤ 5 * Real.pi / 4 → (upper < target ∨ target < lower) → IntervalIntegrable kernel volume lower upper := by
    intro lower upper ordered lower_bound upper_bound side
    exact (banachContourCauchy_intervalIntegrable first (first_near.trans_lt radius_small) target_near
      ordered lower_bound upper_bound side).sub
      (banachContourCauchy_intervalIntegrable second (second_near.trans_lt radius_small) target_near
        ordered lower_bound upper_bound side)
  have edge_integrable := integrable (-Real.pi) (target - Real.pi)
    (by linarith) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inl (by linarith [Real.pi_pos]))
  have left_integrable := integrable (target - Real.pi) (target - target)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inl (by linarith))
  have right_integrable := integrable (target + target) (-Real.pi + 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inr (by linarith))
  have window := periodic_truncated_integral_window_eq periodic edge_integrable left_integrable right_integrable
  have centered := contourCauchyKernel_parameter_truncated_bound first second radius_nonneg radius_small
    first_near second_near target target_pos (by linarith [Real.pi_pos] : target ≤ Real.pi)
  have fixed_bound : ‖(∫ source in (-Real.pi)..0, kernel source) + ∫ source in (2 * target)..Real.pi, kernel source‖ ≤
      4 * constant * Real.sqrt Real.pi := by
    have endpoint_first : -Real.pi + 2 * Real.pi = Real.pi := by ring
    have endpoint_second : target - Real.pi + 2 * Real.pi = target + Real.pi := by ring
    rw [sub_self, endpoint_first, endpoint_second, ← two_mul target] at window
    rw [window]
    simp only [sub_self, ← two_mul] at centered
    convert centered using 1 <;> dsimp only [constant, chord, kernel] <;> ring
  have strip_integrable := integrable (-2 * target) 0
    (by linarith) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inl target_pos)
  have far_integrable := integrable (-Real.pi) (-2 * target)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inl (by linarith))
  have strip_bound : ‖∫ source in (-2 * target)..0, kernel source‖ ≤ 2 * constant := by
    have estimate := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -2 * target) (b := 0) (C := constant / target) (f := kernel) (fun source membership => by
        have source_mem : source ∈ Ioc (-2 * target) 0 := by
          simpa only [uIoc_of_le (by linarith : -2 * target ≤ 0)] using membership
        have distance : |target - source| = target - source := abs_of_pos (by linarith [source_mem.2])
        have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
          rw [abs_sub_comm source target, distance]
          linarith [source_mem.1, Real.pi_pos]
        have size := contourCauchyKernel_parameter_size first second
          (show target ≠ source by linarith [source_mem.2]) (by linarith : 0 ≤ radius + 2) chord_pos
          (PeriodicC1HolderHalf.norm_le_radius_add_two second second_near)
          (by simpa only [abs_sub_comm target source] using PeriodicC1HolderHalf.chord_bound_of_radius first first_near nearby)
          (by simpa only [abs_sub_comm target source] using PeriodicC1HolderHalf.chord_bound_of_radius second second_near nearby)
        exact size.trans (div_le_div_of_nonneg_left constant_nonneg target_pos (by rw [distance]; linarith [source_mem.2])))
    have length : |(0 : ℝ) - -2 * target| = 2 * target := by rw [abs_of_pos (by linarith)]; ring
    rw [length] at estimate
    convert estimate using 1 <;> field_simp <;> ring
  have adjacent := intervalIntegral.integral_add_adjacent_intervals far_integrable strip_integrable
  have identity : (∫ source in (-Real.pi)..(-2 * target), kernel source) + (∫ source in (2 * target)..Real.pi, kernel source) =
      ((∫ source in (-Real.pi)..0, kernel source) + ∫ source in (2 * target)..Real.pi, kernel source) -
        ∫ source in (-2 * target)..0, kernel source := by rw [← adjacent]; abel
  change ‖(∫ source in (-Real.pi)..(-2 * target), kernel source) + ∫ source in (2 * target)..Real.pi, kernel source‖ ≤ _
  rw [identity]
  apply (norm_sub_le _ _).trans ((add_le_add fixed_bound strip_bound).trans_eq ?_)
  dsimp only [constant, chord]
  ring

end EulerNonuniqueness.Paper
