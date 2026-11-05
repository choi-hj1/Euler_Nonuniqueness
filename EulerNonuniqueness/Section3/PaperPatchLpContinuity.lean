import EulerNonuniqueness.Section3.BoundaryDomainConfinement
import EulerNonuniqueness.General.LocalizedFiniteSumConvergence

noncomputable section

open Set MeasureTheory Filter Function
open scoped Topology ENNReal

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.domain_subset_boundary_label_ball
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time bound : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (patch : Fin 4)
    (control : BoundaryCloseToCircle scales motion time index patch bound)
    (boundSmall : bound ≤ 1) (radiusPositive : 0 < scales.radius (index.val + 1)) :
    motion.domain time index patch ⊆ Metric.closedBall (motion.boundary time index patch 0)
      (4 * scales.radius (index.val + 1)) := by
  intro position member
  have positionBound := evolution.domain_subset_centroid_ball inside index patch control radiusPositive member
  have labelBound := control.boundary_distance_le radiusPositive 0
  change dist position (patchCentroid motion time index patch) ≤
    scales.radius (index.val + 1) * (1 + bound) at positionBound
  have labelDistance : dist (patchCentroid motion time index patch) (motion.boundary time index patch 0) ≤
      scales.radius (index.val + 1) * (1 + bound) := by
    rw [dist_comm, dist_eq_norm]
    exact labelBound
  have triangle := dist_triangle position (patchCentroid motion time index patch) (motion.boundary time index patch 0)
  change dist position (motion.boundary time index patch 0) ≤ 4 * scales.radius (index.val + 1)
  nlinarith [mul_le_mul_of_nonneg_left boundSmall radiusPositive.le]

theorem FinitePatchEvolution.tendsto_eLpNorm_patch_sub_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon base : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (baseInside : base ∈ Icc 0 horizon)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ time ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion time index patch bound)
    (index : Fin count) (patch : Fin 4)
    (separated : ∀ (other : Fin count) (otherPatch : Fin 4), (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary base index patch 0) (motion.boundary base other otherPatch 0)) :
    Tendsto (fun time => eLpNorm (fun position =>
      patchDensity scales motion time index patch position - patchDensity scales motion base index patch position)
      1 volume) (𝓝[Icc 0 horizon] base) (𝓝 0) := by
  let component := fun selected : Fin count × Fin 4 =>
    fun time => patchDensity scales motion time selected.1 selected.2
  let anchor := fun selected : Fin count × Fin 4 => fun time => motion.boundary time selected.1 selected.2 0
  let radius := fun selected : Fin count × Fin 4 => 4 * scales.radius (selected.1.val + 1)
  have supported : ∀ time ∈ Icc 0 horizon, ∀ selected : Fin count × Fin 4,
      support (component selected time) ⊆ Metric.closedBall (anchor selected time) (radius selected) := by
    intro time inside selected position nonzero
    obtain ⟨bound, boundSmall, boundaryControl⟩ := control time inside selected.1 selected.2
    apply evolution.domain_subset_boundary_label_ball inside selected.1 selected.2 boundaryControl boundSmall
      (radiusPositive selected.1)
    by_contra outside
    have zero : component selected time position = 0 := by
      dsimp only [component, patchDensity]
      exact Set.indicator_of_not_mem outside _
    exact nonzero zero
  apply EulerNonuniqueness.General.tendsto_eLpNorm_component_sub_of_localized_finite_sum
    (component := component) (anchor := anchor) (radius := radius) baseInside (index, patch)
  · intro selected
    have positive := radiusPositive selected.1
    dsimp only [radius]
    positivity
  · intro selected
    exact (evolution.2.2.2.2.1 selected.1 selected.2 0).continuousWithinAt baseInside
  · intro other different
    have gap := separated other.1 other.2 different
    dsimp only [radius, anchor]
    convert gap using 1 <;> ring
  · exact supported
  · have total := (evolution.2.2.1 base baseInside).2
    simpa only [component, Fintype.sum_prod_type, patchVorticity, quadrupoleDensity] using total

end EulerNonuniqueness.Paper
