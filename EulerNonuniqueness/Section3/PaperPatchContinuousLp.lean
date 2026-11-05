import EulerNonuniqueness.Section3.PaperPatchLpContinuity
import EulerNonuniqueness.Section3.FinitePatchContinuity

noncomputable section

open Set MeasureTheory Filter Function
open scoped Topology ENNReal

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.continuousInLp_patch_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ time ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion time index patch bound)
    (separated : ∀ time ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary time index patch 0) (motion.boundary time other otherPatch 0))
    (index : Fin count) (patch : Fin 4) {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    ContinuousInLpOn horizon (ENNReal.ofReal exponent) (fun time => patchDensity scales motion time index patch) := by
  apply continuousInLpOn_of_uniform_bound_of_tendsto_one
    (bound := ‖patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4‖)
    (norm_nonneg _) exponentBound
  · intro time inside
    have properties := evolution.2.2.2.1 time inside index patch
    exact patchDensity_memLp scales motion time index patch properties.1 properties.2.1 _
  · intro time _ position
    exact norm_indicator_le_norm_self _ _
  · intro time inside
    exact evolution.tendsto_eLpNorm_patch_sub_of_boundary_gaps inside radiusPositive control index patch
      (fun other otherPatch different => separated time inside index other patch otherPatch different)

theorem FinitePatchEvolution.exists_uniform_domain_support_of_boundary_control
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ time ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion time index patch bound) :
    ∃ radius > (0 : ℝ), ∀ time ∈ Icc 0 horizon, ∀ index patch,
      motion.domain time index patch ⊆ Metric.closedBall 0 radius := by
  classical
  let anchors := fun time => fun selected : Fin count × Fin 4 => motion.boundary time selected.1 selected.2 0
  have anchorsContinuous : ContinuousOn anchors (Icc 0 horizon) := by
    apply continuousOn_pi.mpr
    intro selected
    exact evolution.2.2.2.2.1 selected.1 selected.2 0
  obtain ⟨anchorBound, anchorBounds⟩ := isCompact_Icc.exists_bound_of_continuousOn anchorsContinuous
  let radiusSum := ∑ selected : Fin count × Fin 4, 4 * scales.radius (selected.1.val + 1)
  have radiusSumNonnegative : 0 ≤ radiusSum := Finset.sum_nonneg fun selected _ =>
    mul_nonneg (by norm_num) (radiusPositive selected.1).le
  let radius := max 0 anchorBound + radiusSum + 1
  refine ⟨radius, by dsimp only [radius]; positivity, ?_⟩
  intro time inside index patch position member
  obtain ⟨bound, boundSmall, boundaryControl⟩ := control time inside index patch
  have localBound := evolution.domain_subset_boundary_label_ball inside index patch boundaryControl boundSmall
    (radiusPositive index) member
  have anchorBounded : ‖motion.boundary time index patch 0‖ ≤ anchorBound :=
    (norm_le_pi_norm (anchors time) (index, patch)).trans (anchorBounds time inside)
  have radiusBounded : 4 * scales.radius (index.val + 1) ≤ radiusSum := by
    apply Finset.single_le_sum (fun selected _ => mul_nonneg (by norm_num) (radiusPositive selected.1).le)
      (Finset.mem_univ (index, patch))
  have triangle : ‖position‖ ≤ dist position (motion.boundary time index patch 0) +
      ‖motion.boundary time index patch 0‖ := by
    simpa only [dist_eq_norm, sub_add_cancel] using
      norm_add_le (position - motion.boundary time index patch 0) (motion.boundary time index patch 0)
  change dist position (motion.boundary time index patch 0) ≤ 4 * scales.radius (index.val + 1) at localBound
  change ‖position - 0‖ ≤ radius
  rw [sub_zero]
  dsimp only [radius]
  linarith [le_max_right (0 : ℝ) anchorBound]

end EulerNonuniqueness.Paper
