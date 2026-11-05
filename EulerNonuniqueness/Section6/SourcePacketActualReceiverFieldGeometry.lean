import EulerNonuniqueness.Section6.SourcePacketBallCentroidGeometry
import EulerNonuniqueness.Section5.CascadeRhombusOwnGeometry
import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

theorem source_packet_receiver_field_geometry (path : CascadeInternallyStoppedPath prepared)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (index : Fin count)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference prepared.trajectory.movingFamily.patchMotion time index)
    (differenceUpper : diagonalDifference prepared.trajectory.movingFamily.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2)
    (asymmetrySmall : ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64)
    (lengthSmall : 3 * scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusSmall : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ source : Fin count, scales.radius (source.val + 1) ≤ scales.location (source.val + 1) / 1000) :
    ReferenceCentroidFieldGeometry scales prepared.trajectory.movingFamily.patchMotion time index := by
  let motion := prepared.trajectory.movingFamily.patchMotion
  have lengthPositive := scales.length_pos (index.val + 1)
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have differentSource (source : Fin count) (member : source ∈ Finset.univ.erase index) : source ≠ index :=
    (Finset.mem_erase.mp member).1
  have positive (source : Fin count) (member : source ∈ Finset.univ.erase index) : 0 < referenceSourceDistance scales index source :=
    div_pos (scales.location_distance_pos (fun equality =>
      differentSource source member (Fin.ext (Nat.add_right_cancel equality).symm))) (by norm_num)
  have foreign (source : Fin count) (member : source ∈ Finset.univ.erase index) :=
    path.source_packet_prefix_ball_foreign_geometry inside index lengthSmall radiusLocation source (differentSource source member)
  have diagonalPositive : 0 < diagonalDifference motion time index := (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le differenceLower
  obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape lengthPositive diagonalPositive
    differenceUpper ((le_abs_self _).trans radialSmall)
  have centroidsBounded (patch : Fin 4) : ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤
      3 * scales.length (index.val + 1) := by
    have bound := patchCentroid_distance_le_of_halfDiagonals positiveBound negativeBound asymmetrySmall patch
    linarith
  refine ⟨?_, ?_, positive, ?_, ?_, ?_, ?_, centroidsBounded, ?_, ?_⟩
  · intro receiver source different
    have strict := patchCentroid_pair_strict_eighth_of_rhombus_shape motion time index lengthPositive differenceLower
      radialSmall asymmetrySmall source receiver different
    rw [norm_sub_rev] at strict
    linarith
  · linarith
  · intro source _ patch
    exact prepared.trajectory.domain_subset_centroid_ball scales prepared.radiusIdentity (fun _ => rfl) globalInside source patch
  · intro source member
    have near := (foreign source member).1
    change 2 * (3 * scales.length (index.val + 1)) ≤ referenceSourceDistance scales index source at near
    linarith
  · intro source member
    have locations := scales.location_sum_le_three_distance (show index.val + 1 ≠ source.val + 1 from
      fun equality => differentSource source member (Fin.ext (Nat.add_right_cancel equality).symm))
    unfold referenceSourceDistance
    linarith [radiusLocation source, scales.location_pos (index.val + 1), scales.location_pos (source.val + 1)]
  · intro receiver source member patch
    exact path.source_packet_ball_centroid_geometry inside index lengthSmall source (differentSource source member)
      _ (by rw [mem_closedBall, dist_eq_norm]; exact centroidsBounded receiver) patch
  · intro source member patch position positionInside
    exact (foreign source member).2 _ (mem_closedBall_self (by positivity)) patch position positionInside
  · intro source member
    exact (foreign source member).1

end EulerNonuniqueness.Paper.CascadeInternallyStoppedPath
