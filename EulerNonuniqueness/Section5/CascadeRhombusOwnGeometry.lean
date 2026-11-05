import EulerNonuniqueness.Section5.CascadeRhombusStrictGap
import EulerNonuniqueness.Section5.CascadeStoppedMaterialGeometry

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

theorem rhombus_own_domain_geometry (path : CascadeInternallyStoppedPath prepared)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (index : Fin count)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference prepared.trajectory.movingFamily.patchMotion time index)
    (differenceUpper : diagonalDifference prepared.trajectory.movingFamily.patchMotion time index ≤
      2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2)
    (asymmetrySmall : ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
      scales.length (index.val + 1) / 64)
    (radiusSmall : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (factorSmall : factor ≤ 1 / 8) :
    (∀ first second : Fin 4, first ≠ second → factor * scales.length (index.val + 1) <
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index first -
        patchCentroid prepared.trajectory.movingFamily.patchMotion time index second‖) ∧
    (∀ patch, prepared.trajectory.movingFamily.patchMotion.domain time index patch ⊆
      closedBall (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index)
        (3 * scales.length (index.val + 1))) := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have differencePositive : 0 < diagonalDifference prepared.trajectory.movingFamily.patchMotion time index :=
    (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le differenceLower
  obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape lengthPositive
    differencePositive differenceUpper ((le_abs_self _).trans radialSmall)
  constructor
  · intro first second different
    have strict := patchCentroid_pair_strict_eighth_of_rhombus_shape
      prepared.trajectory.movingFamily.patchMotion time index lengthPositive differenceLower radialSmall asymmetrySmall
      first second different
    have scaled := mul_le_mul_of_nonneg_right factorSmall lengthPositive.le
    exact (by nlinarith : factor * scales.length (index.val + 1) ≤ scales.length (index.val + 1) / 8).trans_lt strict
  · intro patch position member
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
    have bounded := prepared.trajectory.domain_subset_centroid_ball scales prepared.radiusIdentity
      (fun _ => rfl) globalInside index patch member
    have positionBound : ‖position - patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch‖ ≤
        2 * scales.radius (index.val + 1) := by
      simpa only [mem_closedBall, dist_eq_norm] using bounded
    have centerBound := patchCentroid_distance_le_of_halfDiagonals positiveBound negativeBound asymmetrySmall patch
    have triangle := norm_sub_le_norm_sub_add_norm_sub position
      (patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch)
      (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index)
    have bound : ‖position - quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ ≤
        3 * scales.length (index.val + 1) := by linarith
    simpa only [mem_closedBall, dist_eq_norm] using bound

end EulerNonuniqueness.Paper.CascadeInternallyStoppedPath
