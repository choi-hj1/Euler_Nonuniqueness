import EulerNonuniqueness.Section3.ContourRemainderParameter

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem symmetric_kernel_truncated_integral_bound {kernel : ℝ → ℂ} {radius cutoff bound : ℝ}
    (cutoff_pos : 0 < cutoff) (ordered : cutoff ≤ radius) (bound_nonneg : 0 ≤ bound)
    (continuous : ContinuousOn kernel (Icc (-radius) radius \ {0}))
    (symmetric_bound : ∀ source ∈ Ioc cutoff radius,
      ‖kernel source + kernel (-source)‖ ≤ bound * inverseSqrtDistance 0 source) :
    ‖(∫ source in (-radius)..(-cutoff), kernel source) + ∫ source in cutoff..radius, kernel source‖ ≤
      2 * bound * Real.sqrt radius := by
  have radius_pos := cutoff_pos.trans_le ordered
  have positive_continuous : ContinuousOn kernel (Icc cutoff radius) := by
    apply continuous.mono
    intro source membership
    refine ⟨⟨by linarith [membership.1], membership.2⟩, ?_⟩
    simp only [mem_singleton_iff]
    linarith [membership.1]
  have negative_continuous : ContinuousOn (fun source => kernel (-source)) (Icc cutoff radius) := by
    apply continuous.comp continuousOn_neg
    intro source membership
    refine ⟨⟨by linarith [membership.2], by linarith [membership.1]⟩, ?_⟩
    simp only [mem_singleton_iff]
    linarith [membership.1]
  have identity : (∫ source in (-radius)..(-cutoff), kernel source) + (∫ source in cutoff..radius, kernel source) =
      ∫ source in cutoff..radius, kernel source + kernel (-source) := by
    rw [intervalIntegral.integral_add (positive_continuous.intervalIntegrable_of_Icc ordered)
      (negative_continuous.intervalIntegrable_of_Icc ordered), intervalIntegral.integral_comp_neg kernel]
    exact add_comm _ _
  rw [identity]
  exact norm_integral_inverseSqrt_subinterval cutoff_pos.le ordered radius_pos bound_nonneg symmetric_bound

theorem contourCauchyKernel_difference_eq_remainder (first second : PeriodicC1HolderHalf) (target source : ℝ) :
    contourCauchyKernel first.val.1 first.val.2.val.1 target source -
      contourCauchyKernel second.val.1 second.val.2.val.1 target source =
    contourCauchyRemainder first.val.1 first.val.2.val.1 target source -
      contourCauchyRemainder second.val.1 second.val.2.val.1 target source := by
  unfold contourCauchyKernel contourCauchyRemainder
  ring

set_option maxHeartbeats 1000000 in
theorem contourCauchyKernel_parameter_truncated_zero_bound (first second : PeriodicC1HolderHalf)
    {radius cutoff : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius)
    (cutoff_pos : 0 < cutoff) (cutoff_le : cutoff ≤ Real.pi) :
    ‖(∫ source in (-Real.pi)..(-cutoff),
        contourCauchyKernel first.val.1 first.val.2.val.1 0 source -
          contourCauchyKernel second.val.1 second.val.2.val.1 0 source) +
      ∫ source in cutoff..Real.pi,
        contourCauchyKernel first.val.1 first.val.2.val.1 0 source -
          contourCauchyKernel second.val.1 second.val.2.val.1 0 source‖ ≤
      4 * ‖first - second‖ * (1 / (2 / (3 * Real.pi) - radius) +
        (radius + 2) / (2 / (3 * Real.pi) - radius) ^ 2) * Real.sqrt Real.pi := by
  let chord := 2 / (3 * Real.pi) - radius
  let speed := radius + 2
  let constant := ‖first - second‖ * (1 / chord + speed / chord ^ 2)
  have chord_pos : 0 < chord := sub_pos.mpr (radius_small.trans_le (min_le_right _ _))
  have speed_pos : 0 < speed := by dsimp only [speed]; linarith
  have constant_nonneg : 0 ≤ constant := by dsimp only [constant]; positivity
  have first_small := first_near.trans_lt radius_small
  have second_small := second_near.trans_lt radius_small
  have zero_near : |(0 : ℝ)| ≤ Real.pi / 4 := by rw [abs_zero]; positivity
  have continuous : ContinuousOn (fun source => contourCauchyKernel first.val.1 first.val.2.val.1 0 source -
      contourCauchyKernel second.val.1 second.val.2.val.1 0 source) (Icc (-Real.pi) Real.pi \ {0}) := by
    apply ((banachContourCauchy_continuousOn_fixed_window first first_small zero_near).sub
      (banachContourCauchy_continuousOn_fixed_window second second_small zero_near)).mono
    intro source membership
    exact ⟨⟨by linarith [membership.1.1, Real.pi_pos], by linarith [membership.1.2, Real.pi_pos]⟩, membership.2⟩
  have remainder_bound : ∀ source ∈ Icc (-Real.pi) Real.pi, source ≠ 0 →
      ‖contourCauchyRemainder first.val.1 first.val.2.val.1 0 source -
        contourCauchyRemainder second.val.1 second.val.2.val.1 0 source‖ ≤ constant / Real.sqrt |source| := by
    intro source membership distinct
    have nearby : |source - (0 : ℝ)| ≤ 3 * Real.pi / 2 := by
      rw [sub_zero, abs_le]
      constructor <;> linarith [membership.1, membership.2, Real.pi_pos]
    have actual := contourCauchyRemainder_parameter_bound first second distinct speed_pos.le chord_pos
      (PeriodicC1HolderHalf.norm_le_radius_add_two second second_near)
      (PeriodicC1HolderHalf.chord_bound_of_radius first first_near nearby)
      (PeriodicC1HolderHalf.chord_bound_of_radius second second_near nearby)
    simpa only [sub_zero] using actual
  have estimate := symmetric_kernel_truncated_integral_bound cutoff_pos cutoff_le
    (show 0 ≤ 2 * constant by positivity) continuous (fun source membership => by
      have source_pos : 0 < source := cutoff_pos.trans membership.1
      have positive := remainder_bound source ⟨by linarith [membership.2, Real.pi_pos], membership.2⟩ source_pos.ne'
      have negative := remainder_bound (-source) ⟨by linarith [membership.2], by linarith [Real.pi_pos]⟩
        (by linarith : -source ≠ 0)
      rw [contourCauchyKernel_difference_eq_remainder, contourCauchyKernel_difference_eq_remainder]
      apply (norm_add_le _ _).trans ((add_le_add positive negative).trans_eq ?_)
      simp only [abs_neg, abs_of_pos source_pos, inverseSqrtDistance, sub_zero]
      ring)
  convert estimate using 1 <;> dsimp only [constant, chord, speed] <;> ring

end EulerNonuniqueness.Paper
