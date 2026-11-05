import EulerNonuniqueness.Section5.CascadeStoppedMaterialGeometry
import EulerNonuniqueness.Section3.BoundaryDomainConfinement

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

theorem boundary_label_gaps_of_radius_bounds
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (radiusInternal : ∀ index : Fin count,
      scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ index : Fin count,
      scales.radius (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (boundarySmall : ∀ index : Fin count,
      boundaryConstant / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2) ≤ 1)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop)
    (receiver source : Fin count) (first second : Fin 4) (different : (receiver, first) ≠ (source, second)) :
    8 * scales.radius (receiver.val + 1) + 8 * scales.radius (source.val + 1) <
      dist (prepared.trajectory.movingFamily.patchMotion.boundary time receiver first 0)
        (prepared.trajectory.movingFamily.patchMotion.boundary time source second 0) := by
  let motion := prepared.trajectory.movingFamily.patchMotion
  have labelBound (index : Fin count) (patch : Fin 4) :
      dist (motion.boundary time index patch 0) (patchCentroid motion time index patch) ≤
        2 * scales.radius (index.val + 1) := by
    have bound := (path.boundary time inside index patch).boundary_distance_le (radiusPositive index) 0
    have numeric := mul_le_mul_of_nonneg_right (add_le_add_left (boundarySmall index) 1) (radiusPositive index).le
    change ‖motion.boundary time index patch 0 - patchCentroid motion time index patch‖ ≤ _ at bound
    rw [dist_eq_norm]
    nlinarith
  have triangle : dist (patchCentroid motion time receiver first) (patchCentroid motion time source second) ≤
      2 * scales.radius (receiver.val + 1) +
        dist (motion.boundary time receiver first 0) (motion.boundary time source second 0) +
        2 * scales.radius (source.val + 1) := by
    have firstTriangle := dist_triangle (patchCentroid motion time receiver first)
      (motion.boundary time receiver first 0) (patchCentroid motion time source second)
    have secondTriangle := dist_triangle (motion.boundary time receiver first 0)
      (motion.boundary time source second 0) (patchCentroid motion time source second)
    have firstBound := labelBound receiver first
    have secondBound := labelBound source second
    rw [dist_comm (motion.boundary time receiver first 0) (patchCentroid motion time receiver first)] at firstBound
    linarith
  simp only [dist_eq_norm] at triangle ⊢
  by_cases same : receiver = source
  · subst source
    have patchDifferent : first ≠ second := fun equality => different (Prod.ext rfl equality)
    have centers := path.internal_centroid_gap inside receiver first second patchDifferent
    have radius := radiusInternal receiver
    linarith [radiusPositive receiver]
  · have pair := (path.quadrupole_pair_bounds inside receiver source same).1
    have receiverExtent := (path.centroid_extent inside receiver first).le
    have sourceExtent := (path.centroid_extent inside source second).le
    have locations := scales.location_sum_le_three_distance
      (show receiver.val + 1 ≠ source.val + 1 from
        fun equality => same (Fin.ext (Nat.add_right_cancel equality)))
    have firstTriangle := norm_sub_le_norm_sub_add_norm_sub
      (quadrupoleCenter motion time receiver) (patchCentroid motion time receiver first)
      (quadrupoleCenter motion time source)
    have secondTriangle := norm_sub_le_norm_sub_add_norm_sub (patchCentroid motion time receiver first)
      (patchCentroid motion time source second) (quadrupoleCenter motion time source)
    rw [norm_sub_rev (quadrupoleCenter motion time receiver) (patchCentroid motion time receiver first)] at firstTriangle
    have gapPositive : 0 < |scales.location (receiver.val + 1) - scales.location (source.val + 1)| := by
      have positive := scales.location_pos (receiver.val + 1)
      have otherPositive := scales.location_pos (source.val + 1)
      linarith
    linarith [radiusLocation receiver, radiusLocation source]

end EulerNonuniqueness.Paper.CascadeInternallyStoppedPath
