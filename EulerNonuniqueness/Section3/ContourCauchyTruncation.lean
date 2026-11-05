import EulerNonuniqueness.Section3.PeriodicPrincipalValue

open MeasureTheory Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem norm_integral_inverseSqrt_subinterval {integrand : ℝ → ℂ} {cutoff radius bound : ℝ}
    (cutoff_nonneg : 0 ≤ cutoff) (ordered : cutoff ≤ radius) (radius_pos : 0 < radius)
    (bound_nonneg : 0 ≤ bound)
    (majorized : ∀ source ∈ Ioc cutoff radius,
      ‖integrand source‖ ≤ bound * inverseSqrtDistance 0 source) :
    ‖∫ source in cutoff..radius, integrand source‖ ≤ 2 * bound * Real.sqrt radius := by
  have whole_integrable := (inverseSqrtDistance_integrable_zero_right radius_pos).const_mul bound
  have sub_integrable := whole_integrable.mono_set
    (show uIcc cutoff radius ⊆ uIcc 0 radius from by
      rw [uIcc_of_le ordered, uIcc_of_le radius_pos.le]
      exact fun source membership => ⟨cutoff_nonneg.trans membership.1, membership.2⟩)
  have estimate := intervalIntegral.norm_integral_le_of_norm_le
    (show ∀ᵐ source ∂volume.restrict (uIoc cutoff radius),
      ‖integrand source‖ ≤ bound * inverseSqrtDistance 0 source from by
      rw [uIoc_of_le ordered]
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with source membership
      exact majorized source membership) sub_integrable
  have nonnegative : 0 ≤ ∫ source in cutoff..radius, bound * inverseSqrtDistance 0 source := by
    exact intervalIntegral.integral_nonneg ordered
      (fun source _ => mul_nonneg bound_nonneg (inverseSqrtDistance_nonneg 0 source))
  rw [abs_of_nonneg nonnegative] at estimate
  have monotone := intervalIntegral.integral_mono_interval cutoff_nonneg ordered le_rfl
    (show 0 ≤ᵐ[volume.restrict (Ioc 0 radius)] (fun source => bound * inverseSqrtDistance 0 source) from
      Eventually.of_forall (fun source => mul_nonneg bound_nonneg (inverseSqrtDistance_nonneg 0 source)))
    whole_integrable
  apply estimate.trans (monotone.trans_eq ?_)
  rw [intervalIntegral.integral_const_mul, inverseSqrtDistance_integral_zero_right radius_pos]
  ring

theorem contourCauchy_symmetric_kernel_bound {curve tangent : ℝ → ℂ}
    {radius source holder chord : ℝ} (source_pos : 0 < source) (source_le : source ≤ radius)
    (holder_nonneg : 0 ≤ holder) (chord_pos : 0 < chord)
    (derivative : ∀ current ∈ Icc (-radius) radius, HasDerivAt curve (tangent current) current)
    (holder_bound : ∀ first ∈ Icc (-radius) radius, ∀ second ∈ Icc (-radius) radius,
      ‖tangent first - tangent second‖ ≤ holder * Real.sqrt |first - second|)
    (chord_bound : ∀ current ∈ Icc (-radius) radius,
      chord * |current| ≤ ‖curve 0 - curve current‖) :
    ‖contourCauchyKernel curve tangent 0 source + contourCauchyKernel curve tangent 0 (-source)‖ ≤
      (2 * holder / chord) * inverseSqrtDistance 0 source := by
  have radius_pos : 0 < radius := source_pos.trans_le source_le
  have zero_mem : (0 : ℝ) ∈ Icc (-radius) radius := ⟨by linarith, radius_pos.le⟩
  have source_mem : source ∈ Icc (-radius) radius := ⟨by linarith, source_le⟩
  have negative_mem : -source ∈ Icc (-radius) radius := ⟨by linarith, by linarith⟩
  have positive_bound := contourCauchyRemainder_bound_unordered source_pos.ne' holder_nonneg chord_pos
    zero_mem source_mem derivative holder_bound (by simpa only [sub_zero] using chord_bound source source_mem)
  have negative_bound := contourCauchyRemainder_bound_unordered (show -source ≠ 0 by linarith)
    holder_nonneg chord_pos zero_mem negative_mem derivative holder_bound
    (by simpa only [sub_zero] using chord_bound (-source) negative_mem)
  have identity : contourCauchyKernel curve tangent 0 source + contourCauchyKernel curve tangent 0 (-source) =
      contourCauchyRemainder curve tangent 0 source + contourCauchyRemainder curve tangent 0 (-source) := by
    simp only [contourCauchyKernel, contourCauchyRemainder, sub_zero, Complex.ofReal_neg, inv_neg]
    ring
  rw [identity]
  apply (norm_add_le _ _).trans ((add_le_add positive_bound negative_bound).trans_eq ?_)
  simp only [sub_zero, abs_neg, abs_of_pos source_pos, inverseSqrtDistance]
  ring

theorem contourCauchy_truncated_integral_bound {curve tangent : ℝ → ℂ}
    {radius cutoff holder chord : ℝ} (cutoff_pos : 0 < cutoff) (ordered : cutoff ≤ radius)
    (holder_nonneg : 0 ≤ holder) (chord_pos : 0 < chord)
    (derivative : ∀ current ∈ Icc (-radius) radius, HasDerivAt curve (tangent current) current)
    (tangent_continuous : ContinuousOn tangent (Icc (-radius) radius))
    (holder_bound : ∀ first ∈ Icc (-radius) radius, ∀ second ∈ Icc (-radius) radius,
      ‖tangent first - tangent second‖ ≤ holder * Real.sqrt |first - second|)
    (chord_bound : ∀ current ∈ Icc (-radius) radius,
      chord * |current| ≤ ‖curve 0 - curve current‖) :
    ‖(∫ source in (-radius)..(-cutoff), contourCauchyKernel curve tangent 0 source) +
      ∫ source in cutoff..radius, contourCauchyKernel curve tangent 0 source‖ ≤
      (4 * holder / chord) * Real.sqrt radius := by
  have radius_pos := cutoff_pos.trans_le ordered
  have curve_continuous : ContinuousOn curve (Icc (-radius) radius) :=
    fun current membership => (derivative current membership).continuousAt.continuousWithinAt
  have continuous : ContinuousOn (contourCauchyKernel curve tangent 0)
      (Icc (-radius) radius \ {0}) := by
    apply (tangent_continuous.mono diff_subset).div
      (continuousOn_const.sub (curve_continuous.mono diff_subset))
    intro source membership
    have distinct : source ≠ 0 := by simpa only [mem_singleton_iff] using membership.2
    exact norm_ne_zero_iff.mp (ne_of_gt ((mul_pos chord_pos (abs_pos.mpr distinct)).trans_le
      (chord_bound source membership.1)))
  have positive_continuous : ContinuousOn (contourCauchyKernel curve tangent 0) (Icc cutoff radius) := by
    apply continuous.mono
    intro source membership
    refine ⟨⟨by linarith [membership.1], membership.2⟩, ?_⟩
    simp only [mem_singleton_iff]
    linarith [membership.1]
  have negative_continuous : ContinuousOn (fun source => contourCauchyKernel curve tangent 0 (-source))
      (Icc cutoff radius) := by
    apply continuous.comp continuousOn_neg
    intro source membership
    refine ⟨⟨by linarith [membership.2], by linarith [membership.1]⟩, ?_⟩
    simp only [mem_singleton_iff]
    linarith [membership.1]
  have identity : (∫ source in (-radius)..(-cutoff), contourCauchyKernel curve tangent 0 source) +
      (∫ source in cutoff..radius, contourCauchyKernel curve tangent 0 source) =
      ∫ source in cutoff..radius,
        contourCauchyKernel curve tangent 0 source + contourCauchyKernel curve tangent 0 (-source) := by
    rw [intervalIntegral.integral_add (positive_continuous.intervalIntegrable_of_Icc ordered)
      (negative_continuous.intervalIntegrable_of_Icc ordered),
      intervalIntegral.integral_comp_neg (contourCauchyKernel curve tangent 0)]
    exact add_comm _ _
  rw [identity]
  have estimate := norm_integral_inverseSqrt_subinterval cutoff_pos.le ordered radius_pos
    (show 0 ≤ 2 * holder / chord by positivity)
    (fun source membership => contourCauchy_symmetric_kernel_bound
      (cutoff_pos.trans membership.1) membership.2 holder_nonneg chord_pos derivative holder_bound chord_bound)
  convert estimate using 1 <;> ring

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem banachContourCauchy_truncated_integral_bound (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (target : ℝ) {cutoff : ℝ} (cutoff_pos : 0 < cutoff) (cutoff_le : cutoff ≤ Real.pi) :
    ‖(∫ source in (target - Real.pi)..(target - cutoff), contourCauchyKernel data.val.1 data.val.2.val.1 target source) +
      ∫ source in (target + cutoff)..(target + Real.pi), contourCauchyKernel data.val.1 data.val.2.val.1 target source‖ ≤
      (4 * ‖data‖ / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖)) * Real.sqrt Real.pi := by
  let curve := fun source => data.val.1 (source + target)
  let tangent := fun source => data.val.2.val.1 (source + target)
  have derivative : ∀ current ∈ Icc (-Real.pi) Real.pi, HasDerivAt curve (tangent current) current := by
    intro current _
    have actual := (PeriodicC1HolderHalf.hasDerivAt data (current + target)).scomp current
      ((hasDerivAt_id current).add_const target)
    simpa only [Function.comp_apply, id_eq, one_smul, curve, tangent] using actual
  have estimate := contourCauchy_truncated_integral_bound cutoff_pos cutoff_le (norm_nonneg data)
    (sub_pos.mpr (small.trans_le (min_le_right _ _))) derivative
    (data.val.2.val.1.continuous.comp (continuous_id.add continuous_const)).continuousOn
    (fun first _ second _ => by
      simpa only [tangent, add_sub_add_right_eq_sub] using
        PeriodicC1HolderHalf.derivative_holder_bound data (first + target) (second + target))
    (fun current membership => by
      change _ ≤ ‖data.val.1 (0 + target) - data.val.1 (current + target)‖
      rw [zero_add]
      have nearby : |current + target - target| ≤ 3 * Real.pi / 2 := by
        rw [add_sub_cancel_right, abs_le]
        constructor <;> linarith [membership.1, membership.2, Real.pi_pos]
      simpa only [add_sub_cancel_right] using PeriodicC1HolderHalf.chord_bound_extended data nearby)
  have kernel_identity : ∀ source : ℝ, contourCauchyKernel curve tangent 0 source =
      contourCauchyKernel data.val.1 data.val.2.val.1 target (source + target) := by
    intro source
    simp only [contourCauchyKernel, curve, tangent, zero_add]
  simp_rw [kernel_identity, intervalIntegral.integral_comp_add_right] at estimate
  convert estimate using 1 <;> congr 1 <;> congr 1 <;> congr 1 <;> ring

end EulerNonuniqueness.Paper
