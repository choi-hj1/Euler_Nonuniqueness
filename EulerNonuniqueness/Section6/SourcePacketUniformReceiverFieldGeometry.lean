import EulerNonuniqueness.Section6.SourcePacketActualReceiverFieldGeometry
import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_actual_receiver_field_geometry (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant shapeRadius factor monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, threshold ≤ 1 / 2 → factor ≤ 1 / 8 →
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    ∀ time ∈ Icc 0 finish,
    ReferenceCentroidFieldGeometry {scales with frequency := frequency}
      prepared.trajectory.movingFamily.patchMotion time index := by
  filter_upwards [scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound
      alphaPositive rootPositive boundaryNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 3000)]
    with frequency joint geometry lengths
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius factor monitor count prepared path
    thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside
  let changed : Scales := {scales with frequency := frequency}
  have controls := joint prepared path thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall
    time inside
  have lengthPositive := changed.length_pos (index.val + 1)
  have diagonal := abs_le.mp controls.1
  have lower : changed.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference prepared.trajectory.movingFamily.patchMotion time index := by
    have multiplied := (le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp (show (3 / 4 : ℝ) ≤
      diagonalDifference prepared.trajectory.movingFamily.patchMotion time index / changed.length (index.val + 1) ^ 2 by
      linarith [diagonal.1])
    nlinarith [sq_nonneg (changed.length (index.val + 1))]
  have upper : diagonalDifference prepared.trajectory.movingFamily.patchMotion time index ≤
      2 * changed.length (index.val + 1) ^ 2 := by
    have multiplied := (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mp (show
      diagonalDifference prepared.trajectory.movingFamily.patchMotion time index / changed.length (index.val + 1) ^ 2 ≤
        (5 / 4 : ℝ) by linarith [diagonal.2])
    nlinarith [sq_nonneg (changed.length (index.val + 1))]
  have lengthSmall : 3 * changed.length (index.val + 1) ≤ changed.location (index.val + 1) / 1000 := by
    have bound := (lengths (index.val + 1)).le
    change changed.length (index.val + 1) ≤ (1 / 3000 : ℝ) * changed.location (index.val + 1) at bound
    linarith
  exact path.source_packet_receiver_field_geometry ⟨inside.1, inside.2.trans finishBound⟩ index lower upper
    (radialSmall time inside) (by linarith [controls.2]) lengthSmall
    (by simpa using (geometry (index.val + 1)).2.1)
    (fun source => (geometry (source.val + 1)).2.2.2)

end EulerNonuniqueness.Paper
