import EulerNonuniqueness.Section6.SourcePacketPrefixBallGeometry

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

theorem source_packet_ball_centroid_geometry (path : CascadeInternallyStoppedPath prepared)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (index : Fin count)
    {radius : ℝ} (radiusSmall : radius ≤ scales.location (index.val + 1) / 1000)
    (source : Fin count) (different : source ≠ index) :
    ∀ position ∈ closedBall (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index) radius,
    ∀ patch, |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8 ≤
      ‖position - patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch‖ := by
  intro position positionInside patch
  have locations := scales.location_sum_le_three_distance (show index.val + 1 ≠ source.val + 1 from
    fun equality => different (Fin.ext (Nat.add_right_cancel equality).symm))
  have positionBound : ‖position - quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ ≤ radius := by
    simpa only [mem_closedBall, dist_eq_norm] using positionInside
  have sourceExtent := path.centroid_extent inside source patch
  have centers := (path.quadrupole_pair_bounds inside index source different.symm).1
  have first := norm_sub_le_norm_sub_add_norm_sub
    (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index) position
    (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source)
  rw [norm_sub_rev (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index) position] at first
  have second := norm_sub_le_norm_sub_add_norm_sub position
    (patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch)
    (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source)
  linarith [scales.location_pos (index.val + 1), scales.location_pos (source.val + 1)]

end EulerNonuniqueness.Paper.CascadeInternallyStoppedPath
