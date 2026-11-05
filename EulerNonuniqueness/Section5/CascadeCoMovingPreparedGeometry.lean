import EulerNonuniqueness.Section5.CascadeCoMovingPreparedPair
import EulerNonuniqueness.Section3.MovingCentroidGaugeDisjointness
import EulerNonuniqueness.Section6.MovingPatchCenterGap

noncomputable section

open Set Metric
open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem CascadeCoMovingPreparedPair.cascadeGeometry_of_comoving_monitors
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeCoMovingPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (rootOne : 1 ≤ scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (radiusLocation : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (internal : ∀ time ∈ Icc (0 : ℝ) 1, ∀ receiver source,
      cascadeInternalGapMonitor scales factor receiver source (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (extent : ∀ time ∈ Icc (0 : ℝ) 1, ∀ label,
      cascadeExtentMonitor scales label (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (lower : ∀ time ∈ Icc (0 : ℝ) 1, ∀ first second,
      cascadeAnchorLowerMonitor scales first second (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (upper : ∀ time ∈ Icc (0 : ℝ) 1, ∀ first second,
      cascadeAnchorUpperMonitor scales first second (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (anchor : ∀ time ∈ Icc (0 : ℝ) 1, ∀ index,
      cascadeAnchorNormMonitor index (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0) :
    CascadeGeometry scales prepared.trajectory.movingFamily.patchMotion (max 2 boundaryConstant) 4 := by
  have control := prepared.analyticControl 1 (by norm_num) le_rfl internal extent lower anchor
  have centroidIdentity (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) (index : Fin count) (patch : Fin 4) :
      patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch =
        prepared.trajectory.movingFamily.cascadeCenters time (index, patch) := by
    rw [FiniteMovingPatchFamily.patchCentroid_eq]
    change (prepared.trajectory.movingPatch (finProdFinEquiv (index, patch))).centroid time = _
    exact prepared.trajectory.movingPatch_centroid_eq_center_of_initial_circles (fun _ => rfl)
      (show time ∈ Ioo (-(1 : ℝ)) 3 from ⟨by linarith [inside.1], by linarith [inside.2]⟩)
      (finProdFinEquiv (index, patch))
  have centerIdentity (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) (index : Fin count) :
      quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index =
        cascadeBlockCenter (prepared.trajectory.movingFamily.cascadeCenters time) index := by
    unfold quadrupoleCenter cascadeBlockCenter
    congr 1
    apply Finset.sum_congr rfl
    intro patch _
    exact centroidIdentity time inside index patch
  have patchOffset (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) (index : Fin count) (patch : Fin 4) :
      ‖(prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).center time -
        cascadeBlockCenter (prepared.trajectory.movingFamily.cascadeCenters time) index‖ ≤
          scales.location (index.val + 1) / 100 :=
    sub_nonpos.mp (extent time inside (index, patch))
  refine ⟨prepared.trajectory.patchesDisjoint_on_interval (by norm_num), ?_, ?_⟩
  · intro time inside index patch
    constructor
    · obtain ⟨relabeling, periodic, relabelingBound, error⟩ := (control.2 time inside).2.2 index patch
      refine ⟨relabeling, periodic, relabelingBound, error.mono ?_⟩
      have squareOne : (1 : ℝ) ≤ scaleRoot ^ 2 := by nlinarith
      have coefficient : boundaryConstant / scaleRoot ^ 2 ≤ max 2 boundaryConstant :=
        (div_le_self boundaryNonnegative squareOne).trans (le_max_right _ _)
      simpa only [div_eq_mul_inv, mul_inv_rev, inv_pow, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right coefficient (sq_nonneg ((scales.omega (index.val + 1))⁻¹))
    · intro position member
      have sourceBound := (prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).domain_subset_ball_two_radius time member
      rw [mem_ball, dist_eq_norm] at sourceBound
      change ‖position - (prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).center time‖ <
        2 * prepared.configuration.radius (finProdFinEquiv (index, patch)) at sourceBound
      rw [prepared.radiusIdentity] at sourceBound
      have firstTriangle := norm_add_le
        ((prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).center time -
          cascadeBlockCenter (prepared.trajectory.movingFamily.cascadeCenters time) index)
        (cascadeBlockCenter (prepared.trajectory.movingFamily.cascadeCenters time) index)
      rw [sub_add_cancel] at firstTriangle
      have anchorBound := sub_nonpos.mp (anchor time inside index)
      have secondTriangle := norm_add_le
        (position - (prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).center time)
        ((prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).center time)
      rw [sub_add_cancel] at secondTriangle
      rw [mem_closedBall, dist_zero_right]
      linarith [patchOffset time inside index patch, radiusLocation index, scales.location_le_one (index.val + 1)]
  · intro time inside index other different
    have lowerBound := lower time inside index other
    have upperBound := upper time inside index other
    rw [cascadeAnchorLowerMonitor, if_neg different] at lowerBound
    rw [cascadeAnchorUpperMonitor, if_neg different] at upperBound
    rw [centerIdentity time inside index, centerIdentity time inside other]
    exact ⟨(div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (le_max_left _ _)).trans
      (sub_nonpos.mp lowerBound),
      (sub_nonpos.mp upperBound).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))⟩

end EulerNonuniqueness.Paper

