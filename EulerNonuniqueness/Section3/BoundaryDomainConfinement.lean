import EulerNonuniqueness.Section3.FinitePatchSupport

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem HasC1HalfBound.norm_le {range : Type*} [NormedAddCommGroup range] [NormedSpace ℝ range]
    {curve : ℝ → range} {bound : ℝ} (control : HasC1HalfBound curve bound) (angle : ℝ) :
    ‖curve angle‖ ≤ bound := by
  obtain ⟨_, valueBound, derivativeBound, holderBound, _, derivativeNonnegative,
    holderNonnegative, totalBound, valueControl, _, _⟩ := control
  exact (valueControl angle).trans (by linarith)

theorem BoundaryCloseToCircle.normalizedBoundary_norm_le {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {time bound : ℝ} {index : Fin count} {patch : Fin 4}
    (control : BoundaryCloseToCircle scales motion time index patch bound) (angle : ℝ) :
    ‖normalizedBoundary scales motion time index patch angle‖ ≤ 1 + bound := by
  obtain ⟨relabeling, _, _, differenceControl⟩ := control
  have unitNorm : ‖Complex.exp (Complex.I * (angle + relabeling angle : ℝ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have triangle := norm_add_le
    (normalizedBoundary scales motion time index patch angle -
      Complex.exp (Complex.I * (angle + relabeling angle : ℝ)))
    (Complex.exp (Complex.I * (angle + relabeling angle : ℝ)))
  rw [sub_add_cancel, unitNorm] at triangle
  exact triangle.trans (by linarith [differenceControl.norm_le angle])

theorem BoundaryCloseToCircle.boundary_distance_le {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {time bound : ℝ} {index : Fin count} {patch : Fin 4}
    (control : BoundaryCloseToCircle scales motion time index patch bound)
    (radiusPositive : 0 < scales.radius (index.val + 1)) (angle : ℝ) :
    ‖motion.boundary time index patch angle - patchCentroid motion time index patch‖ ≤
      scales.radius (index.val + 1) * (1 + bound) := by
  have rotationUnit : ‖Complex.exp (-Complex.I * (patchSign patch * scales.amplitude *
      scales.omega (index.val + 1) ^ 4 * time / 2 : ℝ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, neg_zero,
      Complex.ofReal_re, Complex.neg_im, Complex.I_im, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, Real.exp_zero]
  have identity : ‖normalizedBoundary scales motion time index patch angle‖ =
      ‖motion.boundary time index patch angle - patchCentroid motion time index patch‖ /
        scales.radius (index.val + 1) := by
    rw [normalizedBoundary, norm_mul, rotationUnit, one_mul, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos radiusPositive]
  have estimate := control.normalizedBoundary_norm_le angle
  rw [identity] at estimate
  nlinarith [(div_le_iff₀ radiusPositive).mp estimate]

theorem FinitePatchEvolution.domain_subset_centroid_ball {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon time bound : ℝ} (evolution : FinitePatchEvolution scales motion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count) (patch : Fin 4)
    (control : BoundaryCloseToCircle scales motion time index patch bound)
    (radiusPositive : 0 < scales.radius (index.val + 1)) :
    motion.domain time index patch ⊆ Metric.closedBall (patchCentroid motion time index patch)
      (scales.radius (index.val + 1) * (1 + bound)) := by
  have properties := evolution.2.2.2.1 time inside index patch
  apply properties.2.1.subset_closedBall_of_frontier_subset
  intro position member
  rw [← properties.2.2.2.1] at member
  obtain ⟨angle, rfl⟩ := member
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact control.boundary_distance_le radiusPositive angle

end EulerNonuniqueness.Paper
