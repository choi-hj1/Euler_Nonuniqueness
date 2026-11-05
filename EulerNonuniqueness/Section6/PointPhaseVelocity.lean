import EulerNonuniqueness.Section6.PointShapeCoordinates

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2 Set

attribute [local fun_prop] ContDiffAt.sin ContDiffAt.cos

theorem positive_point_log_im_eq_rotation (coefficient : ℝ) {positive negative : ℂ}
    (positiveNonzero : positive ≠ 0) (negativeNonzero : negative ≠ 0)
    (squaresNonzero : star positive ^ 2 - star negative ^ 2 ≠ 0) (normOrder : ‖negative‖ < ‖positive‖) :
    (positivePointVelocity coefficient positive negative / positive).im =
      rotationVelocity (coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2))
        (pointShapeRatio positive negative) (pointShapeAngle positive negative) := by
  have ratioPositive : 0 < pointShapeRatio positive negative :=
    div_pos (sq_pos_of_pos (norm_pos_iff.mpr negativeNonzero)) (sq_pos_of_pos (norm_pos_iff.mpr positiveNonzero))
  have ratioBelow : pointShapeRatio positive negative < 1 := by
    apply (div_lt_one (sq_pos_of_pos (norm_pos_iff.mpr positiveNonzero))).mpr
    nlinarith [norm_nonneg negative]
  have actual := (point_logarithmic_velocities_in_shape coefficient positiveNonzero negativeNonzero squaresNonzero
    ratioPositive ratioBelow rfl (point_unwrapped_shape_phase_identity positive negative)).1
  rw [actual]
  exact (shape_logarithmic_velocity_components _ ratioPositive ratioBelow).2.2

theorem exists_uniform_point_rotation_error_bound :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ frequency : ℝ, ∀ point : ℝ × ℝ,
      ‖point‖ < radius →
      |rotationVelocity frequency (shapeChartRatio point) (shapeChartAngle point) + frequency| ≤
        bound * |frequency| * ‖point‖ := by
  have denominatorNonzero : 1 + rhombusRatio ^ 2 + 2 * rhombusRatio ≠ 0 := by
    have positive := rhombusRatio_pos
    positivity
  have smooth : ContDiffAt ℝ 1 (fun point : ℝ × ℝ =>
      rotationVelocity 1 (shapeChartRatio point) (shapeChartAngle point)) 0 := by
    unfold rotationVelocity shapeChartRatio shapeChartAngle
    fun_prop (disch := simp_all)
  obtain ⟨bound, neighborhood, neighborhoodMember, estimate⟩ := smooth.exists_lipschitzOnWith
  obtain ⟨radius, radiusPositive, ballInside⟩ := Metric.mem_nhds_iff.mp neighborhoodMember
  refine ⟨bound, bound.coe_nonneg, radius, radiusPositive, ?_⟩
  intro frequency point small
  have inside : point ∈ neighborhood := ballInside (by simpa only [Metric.mem_ball, dist_zero_right] using small)
  have atZero : rotationVelocity 1 (shapeChartRatio 0) (shapeChartAngle 0) = -1 := by
    simpa only [shapeChartRatio, shapeChartAngle, Prod.fst_zero, Prod.snd_zero, add_zero, sub_zero, mul_zero,
      mul_one] using rotationVelocity_at_rhombus (1 : ℝ)
  have control := estimate.norm_sub_le inside (mem_of_mem_nhds neighborhoodMember)
  rw [atZero] at control
  simp only [sub_neg_eq_add, sub_zero, Real.norm_eq_abs] at control
  have scaled := mul_le_mul_of_nonneg_left control (abs_nonneg frequency)
  have identity : rotationVelocity frequency (shapeChartRatio point) (shapeChartAngle point) + frequency =
      frequency * (rotationVelocity 1 (shapeChartRatio point) (shapeChartAngle point) + 1) := by
    unfold rotationVelocity
    ring
  rw [identity, abs_mul]
  exact scaled.trans_eq (by ring)

end EulerNonuniqueness.Section6
