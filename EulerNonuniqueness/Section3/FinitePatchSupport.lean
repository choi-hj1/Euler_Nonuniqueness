import EulerNonuniqueness.Section3.FinitePatchBounds
import EulerNonuniqueness.General.BoundaryConfinement

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem measurable_patchVorticity {count : ℕ} (scales : Scales) (motion : PatchMotion count) (time : ℝ)
    (domainMeasurable : ∀ index patch, MeasurableSet (motion.domain time index patch)) :
    Measurable (patchVorticity scales motion time) := by
  unfold patchVorticity quadrupoleDensity
  exact Finset.measurable_sum Finset.univ (fun index _ =>
    Finset.measurable_sum Finset.univ (fun patch _ =>
      measurable_const.indicator (domainMeasurable index patch)))

theorem FinitePatchEvolution.measurable_vorticity {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon time : ℝ} (evolution : FinitePatchEvolution scales motion horizon)
    (inside : time ∈ Icc 0 horizon) : Measurable (patchVorticity scales motion time) :=
  measurable_patchVorticity scales motion time
    (fun index patch => (evolution.2.2.2.1 time inside index patch).1.measurableSet)

theorem support_patchVorticity_subset_of_boundary_bound {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) {radius : ℝ}
    (bounded : ∀ index patch, Bornology.IsBounded (motion.domain time index patch))
    (frontierEqual : ∀ index patch, range (motion.boundary time index patch) = frontier (motion.domain time index patch))
    (boundaryBounded : ∀ index patch angle, motion.boundary time index patch angle ∈ Metric.closedBall 0 radius) :
    Function.support (patchVorticity scales motion time) ⊆ Metric.closedBall 0 radius := by
  have domainSubset (index : Fin count) (patch : Fin 4) :
      motion.domain time index patch ⊆ Metric.closedBall 0 radius := by
    apply (bounded index patch).subset_closedBall_of_frontier_subset
    intro position inside
    rw [← frontierEqual index patch] at inside
    obtain ⟨angle, rfl⟩ := inside
    exact boundaryBounded index patch angle
  intro position nonzero
  by_contra outside
  have densityZero (index : Fin count) (patch : Fin 4) : patchDensity scales motion time index patch position = 0 := by
    exact indicator_of_not_mem (fun inside => outside (domainSubset index patch inside)) _
  exact nonzero (by simp only [patchVorticity, quadrupoleDensity, densityZero, Finset.sum_const_zero])

theorem FinitePatchEvolution.support_vorticity_subset_of_boundary_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (boundaryBounded : ∀ index patch angle, motion.boundary time index patch angle ∈ Metric.closedBall 0 radius) :
    Function.support (patchVorticity scales motion time) ⊆ Metric.closedBall 0 radius := by
  have properties := evolution.2.2.2.1 time inside
  exact support_patchVorticity_subset_of_boundary_bound scales motion time
    (fun index patch => (properties index patch).2.1)
    (fun index patch => (properties index patch).2.2.2.1) boundaryBounded

end EulerNonuniqueness.Paper
