import EulerNonuniqueness.Section6.FinitePatchDeformationError
import Mathlib.Analysis.Complex.Isometry

noncomputable section

open Set MeasureTheory
open scoped symmDiff

namespace EulerNonuniqueness.Section6

theorem integral_centeredBall_complex_square (radius : ℝ) :
    (∫ position in Metric.ball (0 : ℂ) radius, position ^ 2) = 0 := by
  let quarter : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩
  let rotation := rotation quarter
  have substitution := rotation.measurePreserving.setIntegral_preimage_emb
    rotation.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun position : ℂ => position ^ 2) (Metric.ball (0 : ℂ) radius)
  have preimage : rotation ⁻¹' Metric.ball (0 : ℂ) radius = Metric.ball (0 : ℂ) radius := by
    ext position
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, rotation.norm_map]
  rw [preimage] at substitution
  have square (position : ℂ) : (rotation position) ^ 2 = -(position ^ 2) := by
    simp [rotation, quarter, rotation_apply, mul_pow]
  simp_rw [square] at substitution
  rw [integral_neg] at substitution
  linear_combination (-1 / 2 : ℂ) * substitution

theorem integral_ball_centered_complex_square (center : ℂ) (radius : ℝ) :
    (∫ position in Metric.ball center radius, (position - center) ^ 2) = 0 := by
  have substitution := (measurePreserving_add_left (volume : Measure ℂ) center).setIntegral_preimage_emb
    (Homeomorph.addLeft center).toMeasurableEquiv.measurableEmbedding
    (fun position : ℂ => (position - center) ^ 2) (Metric.ball center radius)
  have preimage : (fun position : ℂ => center + position) ⁻¹' Metric.ball center radius =
      Metric.ball (0 : ℂ) radius := by
    ext position
    simp [Metric.mem_ball, dist_eq_norm]
  rw [preimage] at substitution
  simpa only [add_sub_cancel_left, integral_centeredBall_complex_square] using substitution.symm

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

theorem domain_centered_complex_second_moment_deformation_bound {count : ℕ}
    {configuration : FiniteContourConfiguration count} (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count)
    (small : ‖flow.shape time index - standardCircleBanach‖ ≤ 1 / 16) :
    ‖∫ position in flow.domain time index, (position - flow.centroid time index) ^ 2‖ ≤
      128 * Real.pi * configuration.radius index ^ 4 *
        ‖flow.shape time index - standardCircleBanach‖ := by
  let center := flow.centroid time index
  let radius := configuration.radius index
  have radiusPositive : 0 < radius := configuration.radius_pos index
  have geometry := flow.domain_centroid_deformation_geometry inside index small
  have diskBounded : Metric.ball center radius ⊆ Metric.closedBall center (2 * radius) := by
    intro position member
    have bound : ‖position - center‖ < radius := by simpa [Metric.mem_ball, dist_eq_norm] using member
    simpa [Metric.mem_closedBall, dist_eq_norm] using bound.le.trans (by linarith : radius ≤ 2 * radius)
  have unionBounded : flow.domain time index ∪ Metric.ball center radius ⊆
      Metric.closedBall center (2 * radius) := union_subset geometry.2.1 diskBounded
  have differenceBounded := symmDiff_subset_union.trans unionBounded
  have finite : volume (flow.domain time index ∆ Metric.ball center radius) < ⊤ :=
    lt_of_le_of_lt (measure_mono differenceBounded) measure_closedBall_lt_top
  have continuousSquare : Continuous (fun position : ℂ => (position - center) ^ 2) :=
    (continuous_id.sub continuous_const).pow 2
  have integrableSquare : IntegrableOn (fun position : ℂ => (position - center) ^ 2)
      (Metric.closedBall center (2 * radius)) := continuousSquare.continuousOn.integrableOn_compact
    (isCompact_closedBall center (2 * radius))
  have estimate := Section6.norm_patch_integral_difference_le
    (flow.domain_isOpen time index).measurableSet measurableSet_ball finite
    (integrableSquare.mono_set geometry.2.1) (integrableSquare.mono_set diskBounded)
    (bound := 4 * radius ^ 2) (fun position member => by
      have bound : ‖position - center‖ ≤ 2 * radius := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using differenceBounded member
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) bound 2).trans_eq (by ring))
  rw [Section6.integral_ball_centered_complex_square, sub_zero] at estimate
  apply estimate.trans
  have multiplied := mul_le_mul_of_nonneg_right geometry.2.2 (by positivity : 0 ≤ 4 * radius ^ 2)
  convert multiplied using 1 <;> dsimp only [radius] <;> ring

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
