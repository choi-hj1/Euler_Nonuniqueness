import Mathlib

noncomputable section

open Set Metric
open scoped Topology

namespace EulerNonuniqueness.General

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem exists_closedBall_fderiv_lipschitz_of_contDiffAt_two
    {function : Domain → Range} {point : Domain} (smooth : ContDiffAt ℝ 2 function point) :
    ∃ radius > 0, ∃ constant : NNReal,
      LipschitzOnWith constant (fderiv ℝ function) (closedBall point radius) := by
  have derivativeSmooth : ContDiffAt ℝ 1 (fderiv ℝ function) point := smooth.fderiv_right (by norm_num)
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ := derivativeSmooth.exists_lipschitzOnWith
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp nearby
  refine ⟨radius / 2, by positivity, constant, lipschitz.mono ?_⟩
  intro current member
  apply contained
  exact (mem_closedBall.mp member).trans_lt (by linarith)

theorem exists_closedBall_fderiv_bound_of_contDiffAt_two
    {function : Domain → Range} {point : Domain} (smooth : ContDiffAt ℝ 2 function point) :
    ∃ radius > 0, ∃ constant ≥ 0,
      (∀ current ∈ closedBall point radius, ‖fderiv ℝ function current‖ ≤ constant) ∧
      ∀ first ∈ closedBall point radius, ∀ second ∈ closedBall point radius,
        ‖fderiv ℝ function first - fderiv ℝ function second‖ ≤ constant * ‖first - second‖ := by
  obtain ⟨radius, positive, lipschitzConstant, lipschitz⟩ :=
    exists_closedBall_fderiv_lipschitz_of_contDiffAt_two smooth
  let constant : ℝ := ‖fderiv ℝ function point‖ + (lipschitzConstant : ℝ) * radius + lipschitzConstant
  have lipschitzLe : (lipschitzConstant : ℝ) ≤ constant := by
    dsimp only [constant]
    nlinarith [norm_nonneg (fderiv ℝ function point), lipschitzConstant.coe_nonneg]
  refine ⟨radius, positive, constant, by dsimp only [constant]; positivity, ?_, ?_⟩
  · intro current member
    have nearby := lipschitz.norm_sub_le member (mem_closedBall_self positive.le)
    have distanceBound : ‖current - point‖ ≤ radius := by
      exact (dist_eq_norm current point) ▸ (mem_closedBall.mp member)
    calc
      ‖fderiv ℝ function current‖ ≤ ‖fderiv ℝ function current - fderiv ℝ function point‖ +
          ‖fderiv ℝ function point‖ := by
        calc
          _ = ‖(fderiv ℝ function current - fderiv ℝ function point) + fderiv ℝ function point‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      _ ≤ (lipschitzConstant : ℝ) * radius + ‖fderiv ℝ function point‖ := by
        gcongr
        exact nearby.trans (mul_le_mul_of_nonneg_left distanceBound lipschitzConstant.coe_nonneg)
      _ ≤ constant := by dsimp only [constant]; linarith [lipschitzConstant.coe_nonneg]
  · intro first firstMember second secondMember
    exact (lipschitz.norm_sub_le firstMember secondMember).trans
      (mul_le_mul_of_nonneg_right lipschitzLe (norm_nonneg _))

end EulerNonuniqueness.General
