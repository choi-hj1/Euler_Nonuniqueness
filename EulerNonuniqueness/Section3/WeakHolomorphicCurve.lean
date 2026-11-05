import Mathlib.Analysis.Complex.CauchyIntegral

open Set Metric Filter Complex
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem circleIntegral_map_complex (evaluation : E →L[ℂ] ℂ) {function : ℂ → E}
    {center : ℂ} {radius : ℝ} (integrable : CircleIntegrable function center radius) :
    (∮ parameter in C(center, radius), evaluation (function parameter)) =
      evaluation (∮ parameter in C(center, radius), function parameter) := by
  unfold circleIntegral
  simpa only [map_smul] using evaluation.intervalIntegral_comp_comm integrable.out

theorem weakHolomorphicCurve_cauchy {Label : Type*} (evaluation : Label → E →L[ℂ] ℂ)
    (separates : ∀ first second : E, (∀ label, evaluation label first = evaluation label second) → first = second)
    {function : ℂ → E} {center : ℂ} {radius : ℝ} (positive : 0 < radius)
    (continuous : ContinuousOn function (closedBall center radius))
    (holomorphic : ∀ label, DifferentiableOn ℂ (fun parameter => evaluation label (function parameter))
      (ball center radius)) {position : ℂ} (inside : position ∈ ball center radius) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ parameter in C(center, radius), (parameter - position)⁻¹ • function parameter) = function position := by
  have kernel_integrable : CircleIntegrable (fun parameter => (parameter - position)⁻¹ • function parameter)
      center radius := by
    apply ContinuousOn.circleIntegrable positive.le
    refine ((continuousOn_id.sub continuousOn_const).inv₀ ?_).smul
      (continuous.mono sphere_subset_closedBall)
    intro parameter member
    apply sub_ne_zero.mpr
    intro equal
    change parameter = position at equal
    subst parameter
    exact (mem_ball.mp inside).ne (mem_sphere.mp member)
  apply separates
  intro label
  rw [map_smul, ← circleIntegral_map_complex (evaluation label) kernel_integrable]
  simp_rw [map_smul]
  apply DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul
    (f := fun parameter => evaluation label (function parameter)) _ inside
  exact ⟨holomorphic label, by
    rw [closure_ball center positive.ne']
    exact (evaluation label).continuous.comp_continuousOn continuous⟩

theorem analyticAt_of_separating_evaluations {Label : Type*} (evaluation : Label → E →L[ℂ] ℂ)
    (separates : ∀ first second : E, (∀ label, evaluation label first = evaluation label second) → first = second)
    {function : ℂ → E} {center : ℂ} {radius : ℝ≥0} (positive : 0 < radius)
    (continuous : ContinuousOn function (closedBall center radius))
    (holomorphic : ∀ label, DifferentiableOn ℂ (fun parameter => evaluation label (function parameter))
      (ball center radius)) : AnalyticAt ℂ function center := by
  have integrable : CircleIntegrable function center radius :=
    ContinuousOn.circleIntegrable radius.coe_nonneg (continuous.mono sphere_subset_closedBall)
  apply (hasFPowerSeriesOn_cauchy_integral integrable positive).analyticAt.congr
  filter_upwards [Metric.ball_mem_nhds center positive] with position inside
  exact weakHolomorphicCurve_cauchy evaluation separates positive continuous holomorphic inside

end

end EulerNonuniqueness.Paper
