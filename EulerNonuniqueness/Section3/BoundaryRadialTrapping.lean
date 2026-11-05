import EulerNonuniqueness.Section3.BoundaryDomainConfinement
import EulerNonuniqueness.General.OpenRegionRadialTrapping
import EulerNonuniqueness.Section3.DiskLp

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem BoundaryCloseToCircle.normalizedBoundary_norm_error {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {time bound : ℝ} {index : Fin count} {patch : Fin 4}
    (control : BoundaryCloseToCircle scales motion time index patch bound) (angle : ℝ) :
    |‖normalizedBoundary scales motion time index patch angle‖ - 1| ≤ bound := by
  obtain ⟨relabeling, _, _, differenceControl⟩ := control
  have unitNorm : ‖Complex.exp (Complex.I * (angle + relabeling angle : ℝ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have estimate := (abs_norm_sub_norm_le
    (normalizedBoundary scales motion time index patch angle)
    (Complex.exp (Complex.I * (angle + relabeling angle : ℝ)))).trans (differenceControl.norm_le angle)
  simpa only [unitNorm] using estimate

theorem BoundaryCloseToCircle.boundary_radial_error {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {time bound : ℝ} {index : Fin count} {patch : Fin 4}
    (control : BoundaryCloseToCircle scales motion time index patch bound)
    (radiusPositive : 0 < scales.radius (index.val + 1)) (angle : ℝ) :
    |‖motion.boundary time index patch angle - patchCentroid motion time index patch‖ -
        scales.radius (index.val + 1)| ≤ scales.radius (index.val + 1) * bound := by
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
  have estimate := mul_le_mul_of_nonneg_left (control.normalizedBoundary_norm_error angle) radiusPositive.le
  rw [identity] at estimate
  have algebra : ‖motion.boundary time index patch angle - patchCentroid motion time index patch‖ -
      scales.radius (index.val + 1) = scales.radius (index.val + 1) *
        (‖motion.boundary time index patch angle - patchCentroid motion time index patch‖ /
          scales.radius (index.val + 1) - 1) := by field_simp [radiusPositive.ne']
  rw [algebra, abs_mul, abs_of_pos radiusPositive]
  exact estimate

theorem FinitePatchEvolution.domain_radial_trapping {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon time bound : ℝ} (evolution : FinitePatchEvolution scales motion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count) (patch : Fin 4)
    (control : BoundaryCloseToCircle scales motion time index patch bound)
    (boundNonnegative : 0 ≤ bound) (boundSmall : bound < 1 / 4)
    (radiusPositive : 0 < scales.radius (index.val + 1)) :
    Metric.ball (patchCentroid motion time index patch) (scales.radius (index.val + 1) * (1 - bound)) ⊆
        motion.domain time index patch ∧
      motion.domain time index patch ⊆
        Metric.ball (patchCentroid motion time index patch) (scales.radius (index.val + 1) * (1 + bound)) := by
  have properties := evolution.2.2.2.1 time inside index patch
  have lowerPositive : 0 < scales.radius (index.val + 1) * (1 - bound) := mul_pos radiusPositive (by linarith)
  have upperPositive : 0 < scales.radius (index.val + 1) * (1 + bound) := mul_pos radiusPositive (by linarith)
  apply properties.1.radial_trapping_of_bounded_frontier_and_area properties.2.1
    (patchCentroid motion time index patch) lowerPositive (by nlinarith)
  · intro position member
    rw [← properties.2.2.2.1] at member
    obtain ⟨angle, rfl⟩ := member
    have estimate := (abs_le.mp (control.boundary_radial_error radiusPositive angle)).1
    nlinarith
  · intro position member
    rw [← properties.2.2.2.1] at member
    obtain ⟨angle, rfl⟩ := member
    have estimate := (abs_le.mp (control.boundary_radial_error radiusPositive angle)).2
    nlinarith
  · have area : volume.real (motion.domain time index patch) = Real.pi * scales.radius (index.val + 1) ^ 2 := by
      rw [Measure.real, properties.2.2.1, ENNReal.toReal_ofReal (by positivity)]
    have upperArea : volume.real (Metric.ball (patchCentroid motion time index patch)
        (scales.radius (index.val + 1) * (1 + bound))) =
        Real.pi * (scales.radius (index.val + 1) * (1 + bound)) ^ 2 := by
      rw [Measure.real, volume_complex_ball_of_nonneg _ upperPositive.le, ENNReal.toReal_ofReal (by positivity)]
    have lowerArea : volume.real (Metric.ball (patchCentroid motion time index patch)
        (scales.radius (index.val + 1) * (1 - bound))) =
        Real.pi * (scales.radius (index.val + 1) * (1 - bound)) ^ 2 := by
      rw [Measure.real, volume_complex_ball_of_nonneg _ lowerPositive.le, ENNReal.toReal_ofReal (by positivity)]
    rw [upperArea, lowerArea, area]
    have positive : 0 < Real.pi * scales.radius (index.val + 1) ^ 2 := by positivity
    nlinarith [mul_lt_mul_of_pos_left boundSmall positive]

end EulerNonuniqueness.Paper
