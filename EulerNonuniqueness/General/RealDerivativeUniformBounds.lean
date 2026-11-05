import EulerNonuniqueness.General.LocalDerivativeLipschitz

noncomputable section

open Set Metric

namespace EulerNonuniqueness.General

theorem exists_uniform_real_derivative_ball {function : ℝ → ℝ}
    (smooth : ContDiffAt ℝ 2 function 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
      (∀ point : ℝ, |point| ≤ radius → |deriv function point| ≤ constant) ∧
      ∀ first second : ℝ, |first| ≤ radius → |second| ≤ radius →
        |deriv function first - deriv function second| ≤ constant * |first - second| := by
  obtain ⟨radius, positive, bound, nonnegative, bounded, lipschitz⟩ :=
    exists_closedBall_fderiv_bound_of_contDiffAt_two smooth
  refine ⟨radius, positive, 1 + bound, by linarith, ?_, ?_⟩
  · intro point member
    have inside : point ∈ closedBall (0 : ℝ) radius := by simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using member
    have actual := bounded point inside
    rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs] at actual
    linarith
  · intro first second firstMember secondMember
    have firstInside : first ∈ closedBall (0 : ℝ) radius := by simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using firstMember
    have secondInside : second ∈ closedBall (0 : ℝ) radius := by simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using secondMember
    have actual := lipschitz first firstInside second secondInside
    have evaluation := (fderiv ℝ function first - fderiv ℝ function second).le_opNorm (1 : ℝ)
    simp only [ContinuousLinearMap.sub_apply, fderiv_deriv, norm_one, mul_one, Real.norm_eq_abs] at evaluation
    have actual' := evaluation.trans (by simpa only [Real.norm_eq_abs] using actual)
    exact actual'.trans (by nlinarith [abs_nonneg (first - second)])

end EulerNonuniqueness.General
