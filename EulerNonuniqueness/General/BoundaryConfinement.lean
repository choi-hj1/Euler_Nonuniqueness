import Mathlib

noncomputable section

open Set Metric

theorem Bornology.IsBounded.closure_subset_closedBall_of_frontier_subset
    {region : Set ℂ} (bounded : Bornology.IsBounded region) {center : ℂ} {radius : ℝ}
    (boundary : frontier region ⊆ closedBall center radius) :
    closure region ⊆ closedBall center radius := by
  intro position inside
  rw [mem_closedBall, dist_eq_norm]
  have differentiable : Differentiable ℂ (fun position : ℂ => position - center) :=
    differentiable_id.sub_const center
  exact Complex.norm_le_of_forall_mem_frontier_norm_le bounded differentiable.diffContOnCl
    (fun point boundaryPoint => by simpa only [mem_closedBall, dist_eq_norm] using boundary boundaryPoint) inside

theorem Bornology.IsBounded.subset_closedBall_of_frontier_subset
    {region : Set ℂ} (bounded : Bornology.IsBounded region) {center : ℂ} {radius : ℝ}
    (boundary : frontier region ⊆ closedBall center radius) :
    region ⊆ closedBall center radius :=
  subset_closure.trans (bounded.closure_subset_closedBall_of_frontier_subset boundary)
