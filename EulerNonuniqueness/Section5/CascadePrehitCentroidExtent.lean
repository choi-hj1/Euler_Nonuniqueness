import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation
import EulerNonuniqueness.Section5.CascadeForeignReceiverAlignment

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_prehit_centroid_extent (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {scaleRoot boundaryConstant threshold referenceConstant : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant) :
    ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {shapeRadius factor monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, factor ≤ 1 / 8 →
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish, ∀ patch,
        ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
          quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ ≤
            3 * ({scales with frequency := frequency} : Scales).length (index.val + 1) ∧
        ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index patch -
          quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index‖ ≤
            3 * ({scales with frequency := frequency} : Scales).length (index.val + 1) := by
  filter_upwards [scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative]
    with frequency joint mechanical
  intro orbit sectionTime phase dipoleAngle shapeRadius factor monitor count prepared path factorSmall
    index nonterminal finish finishNonnegative finishBound radialSmall time inside patch
  let changed : Scales := {scales with frequency := frequency}
  have actual := joint prepared path (thresholdSmall.trans (by norm_num)) factorSmall index nonterminal finish
    finishNonnegative finishBound radialSmall time inside
  have lengthPositive := changed.length_pos (index.val + 1)
  have differenceBounds := abs_le.mp actual.1
  have lower : changed.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference prepared.trajectory.movingFamily.patchMotion time index := by
    have scaled := (le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp
      (show (1 / 2 : ℝ) ≤ diagonalDifference prepared.trajectory.movingFamily.patchMotion time index /
        changed.length (index.val + 1) ^ 2 by linarith [differenceBounds.1])
    linarith
  have upper : diagonalDifference prepared.trajectory.movingFamily.patchMotion time index ≤
      2 * changed.length (index.val + 1) ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mp (by linarith [differenceBounds.2])
  obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape lengthPositive
    ((by positivity : 0 < changed.length (index.val + 1) ^ 2 / 2).trans_le lower) upper
      ((le_abs_self _).trans (radialSmall time inside))
  have first := patchCentroid_distance_le_of_halfDiagonals positiveBound negativeBound actual.2.le patch
  have referenceInside : time ∈ Icc (0 : ℝ) 2 :=
    ⟨inside.1, by linarith [inside.2, finishBound, path.stopBound]⟩
  exact ⟨by linarith, (mechanical _ prepared.referenceWitness.evolution prepared.referenceWitness.coarse
    time referenceInside index).1.centroidsBounded patch⟩

end EulerNonuniqueness.Paper
