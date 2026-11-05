import EulerNonuniqueness.Section6.NonlinearShape

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem shapeChartVelocity_frequency_smul (frequency : ℝ) (point : ℝ × ℝ) :
    shapeChartVelocity frequency point = frequency • shapeChartVelocity 1 point := by
  ext <;> simp only [shapeChartVelocity, EulerNonuniqueness.Section2.radialVelocity,
    EulerNonuniqueness.Section2.shapeAngleVelocity, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    <;> ring

theorem exists_uniform_shapeChartVelocity_continuousOn_radius :
    ∃ radius > (0 : ℝ), ∀ (times : Set ℝ) (frequency : ℝ → ℝ) (shape : ℝ → ℝ × ℝ),
      ContinuousOn frequency times → ContinuousOn shape times →
      (∀ time ∈ times, ‖shape time‖ < radius) →
      ContinuousOn (fun time => shapeChartVelocity (frequency time) (shape time)) times := by
  have regularity := (shapeChartVelocity_contDiffAt 1).eventually (by norm_num)
  obtain ⟨radius, radiusPositive, ballInside⟩ := Metric.mem_nhds_iff.mp regularity
  refine ⟨radius, radiusPositive, ?_⟩
  intro times frequency shape frequencyContinuous shapeContinuous small
  have normalized : ContinuousOn (fun time => shapeChartVelocity 1 (shape time)) times := by
    intro time member
    have smooth : ContDiffAt ℝ 2 (shapeChartVelocity 1) (shape time) :=
      ballInside (by simpa only [Metric.mem_ball, dist_zero_right] using small time member)
    exact ContinuousAt.comp_continuousWithinAt (f := shape) smooth.continuousAt (shapeContinuous time member)
  apply (frequencyContinuous.smul normalized).congr
  intro time _
  exact shapeChartVelocity_frequency_smul (frequency time) (shape time)

end EulerNonuniqueness.Section6
