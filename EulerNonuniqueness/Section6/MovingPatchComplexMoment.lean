import EulerNonuniqueness.Section6.PatchSubfamilyComplexMoment

noncomputable section

open Set MeasureTheory
open scoped symmDiff

namespace EulerNonuniqueness.Section6

theorem patch_centered_complex_second_moment_of_trapping {domain : Set ℂ}
    (measurable : MeasurableSet domain) (center centroid : ℂ) {radius deformation : ℝ}
    (radiusPositive : 0 < radius) (deformationNonnegative : 0 ≤ deformation)
    (deformationSmall : deformation ≤ 1 / 16)
    (lower : Metric.ball center (radius * (1 - deformation)) ⊆ domain)
    (upper : domain ⊆ Metric.ball center (radius * (1 + deformation)))
    (area : volume.real domain = Real.pi * radius ^ 2)
    (centered : (∫ position in domain, position - centroid) = 0) :
    ‖∫ position in domain, (position - centroid) ^ 2‖ ≤ 128 * Real.pi * radius ^ 4 * deformation := by
  have geometry := patch_actual_centroid_geometry measurable center centroid radiusPositive deformationNonnegative
    deformationSmall lower upper area centered
  have diskBounded : Metric.ball centroid radius ⊆ Metric.closedBall centroid (2 * radius) := by
    intro position member
    have bound : ‖position - centroid‖ < radius := by simpa [Metric.mem_ball, dist_eq_norm] using member
    simpa [Metric.mem_closedBall, dist_eq_norm] using bound.le.trans (by linarith : radius ≤ 2 * radius)
  have differenceBounded := symmDiff_subset_union.trans (union_subset geometry.2.1 diskBounded)
  have finite : volume (domain ∆ Metric.ball centroid radius) < ⊤ :=
    lt_of_le_of_lt (measure_mono differenceBounded) measure_closedBall_lt_top
  have squareIntegrable : IntegrableOn (fun position : ℂ => (position - centroid) ^ 2)
      (Metric.closedBall centroid (2 * radius)) :=
    (((continuous_id.sub continuous_const).pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall centroid (2 * radius)))
  have estimate := norm_patch_integral_difference_le measurable measurableSet_ball finite
    (squareIntegrable.mono_set geometry.2.1) (squareIntegrable.mono_set diskBounded)
    (bound := 4 * radius ^ 2) (fun position member => by
      have bound : ‖position - centroid‖ ≤ 2 * radius := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using differenceBounded member
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) bound 2).trans_eq (by ring))
  rw [integral_ball_centered_complex_square, sub_zero] at estimate
  apply estimate.trans
  have control := mul_le_mul_of_nonneg_right geometry.2.2 (by positivity : 0 ≤ 4 * radius ^ 2)
  convert control using 1 <;> ring

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem domain_complex_second_moment_point_error_of_trapping (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) (reference center : ℂ)
    {deformation : ℝ} (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16)
    (lower : Metric.ball center (configuration.radius index * (1 - deformation)) ⊆ flow.domain time index)
    (upper : flow.domain time index ⊆ Metric.ball center (configuration.radius index * (1 + deformation))) :
    ‖(∫ position in flow.domain time index, (position - reference) ^ 2) -
        (Real.pi * configuration.radius index ^ 2) • (flow.centroid time index - reference) ^ 2‖ ≤
      128 * Real.pi * configuration.radius index ^ 4 * deformation := by
  rw [flow.domain_complex_second_moment_centroid_identity inside index reference, add_sub_cancel_left]
  exact Section6.patch_centered_complex_second_moment_of_trapping (flow.domain_isOpen time index).measurableSet
    center (flow.centroid time index) (configuration.radius_pos index) deformationNonnegative deformationSmall
    lower upper (flow.domain_area inside index) (flow.domain_centroid_centered_integral inside index)

theorem subfamily_complex_second_moment_point_error_of_trapping (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (selected : Finset (Fin count))
    (reference : ℂ) (centers : Fin count → ℂ) (deformation : Fin count → ℝ)
    (nonnegative : ∀ index ∈ selected, 0 ≤ deformation index)
    (small : ∀ index ∈ selected, deformation index ≤ 1 / 16)
    (lower : ∀ index ∈ selected, Metric.ball (centers index)
      (configuration.radius index * (1 - deformation index)) ⊆ flow.domain time index)
    (upper : ∀ index ∈ selected, flow.domain time index ⊆ Metric.ball (centers index)
      (configuration.radius index * (1 + deformation index))) :
    ‖(∫ position, flow.subfamilyVorticity selected time position • (position - reference) ^ 2) -
        ∑ index ∈ selected, (configuration.density index * (Real.pi * configuration.radius index ^ 2)) •
          (flow.centroid time index - reference) ^ 2‖ ≤
      ∑ index ∈ selected, 128 * |configuration.density index * (Real.pi * configuration.radius index ^ 2)| *
        configuration.radius index ^ 2 * deformation index := by
  rw [flow.integral_subfamilyVorticity_smul selected time (fun position : ℂ => (position - reference) ^ 2)
    (fun index _ => ((((continuous_id.sub continuous_const).pow 2).continuousOn.integrableOn_compact
      (flow.domain_isBounded time index).isCompact_closure).mono_set subset_closure)), ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro index member
  rw [mul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left
    (flow.domain_complex_second_moment_point_error_of_trapping inside index reference (centers index)
      (nonnegative index member) (small index member) (lower index member) (upper index member))
    (abs_nonneg (configuration.density index))).trans_eq
  rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.pi * configuration.radius index ^ 2 by positivity)]
  ring

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
