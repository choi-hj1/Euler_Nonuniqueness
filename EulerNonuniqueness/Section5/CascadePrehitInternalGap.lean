import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_material_prehit_internal_gap (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant shapeRadius factor monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    threshold ≤ 1 / 2 → factor ≤ 1 / 8 →
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    ∀ time ∈ Icc 0 finish,
      (∀ first second : Fin 4, first ≠ second → factor * ({scales with frequency := frequency} : Scales).length (index.val + 1) <
        ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index first -
          patchCentroid prepared.trajectory.movingFamily.patchMotion time index second‖) ∧
      (∀ patch, prepared.trajectory.movingFamily.patchMotion.domain time index patch ⊆
        closedBall (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index)
          (3 * ({scales with frequency := frequency} : Scales).length (index.val + 1))) := by
  filter_upwards [scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound
    alphaPositive rootPositive boundaryNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num)]
    with frequency joint geometry
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius factor monitor count prepared path
    thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time member
  let changed : Scales := {scales with frequency := frequency}
  have actual := joint prepared path thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time member
  have lengthPositive := changed.length_pos (index.val + 1)
  have diagonal := abs_le.mp actual.1
  have lower : changed.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference prepared.trajectory.movingFamily.patchMotion time index := by
    have scaled := (le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp (by linarith [diagonal.1] :
      (1 / 2 : ℝ) ≤ diagonalDifference prepared.trajectory.movingFamily.patchMotion time index / changed.length (index.val + 1) ^ 2)
    linarith
  have upper : diagonalDifference prepared.trajectory.movingFamily.patchMotion time index ≤
      2 * changed.length (index.val + 1) ^ 2 := by
    have scaled := (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mp (by linarith [diagonal.2] :
      diagonalDifference prepared.trajectory.movingFamily.patchMotion time index / changed.length (index.val + 1) ^ 2 ≤ 2)
    exact scaled
  have neutral : ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
      changed.length (index.val + 1) / 64 := by linarith [actual.2]
  exact path.rhombus_own_domain_geometry ⟨member.1, member.2.trans finishBound⟩ index lower upper
    (radialSmall time member) neutral (by simpa only [one_mul] using (geometry (index.val + 1)).2.1) factorSmall

end EulerNonuniqueness.Paper
