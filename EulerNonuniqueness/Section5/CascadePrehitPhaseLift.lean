import EulerNonuniqueness.Section5.CascadeNonterminalPhaseLift
import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_material_prehit_phase_lift (scales : Scales)
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
    ∃ lift : ℝ → ℝ, Continuous lift ∧ lift 0 = phase (index.val + 1) ∧
      ∀ time ∈ Icc 0 finish,
        HasDerivAt lift (-({scales with frequency := frequency} : Scales).omega (index.val + 1) /
          referenceDilation {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion index time +
          referencePhaseError {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion index time) time ∧
        positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index =
          (‖positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift time : ℂ)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative] with frequency frequencyPositive joint
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius factor monitor count prepared path
    thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall
  apply prepared.nonterminal_exists_phase_on_prefix amplitudePositive frequencyPositive
    (by dsimp; linarith) index nonterminal finishNonnegative
  · intro time member source
    change time ∈ Ioo (-(1 : ℝ)) 3
    exact ⟨by linarith [member.1], by linarith [member.2, path.stopBound]⟩
  · intro time member
    have actual := joint prepared path thresholdSmall factorSmall index nonterminal finish finishNonnegative
      finishBound radialSmall time member
    have lower := (abs_le.mp actual.1).1
    have lengthPositive := ({scales with frequency := frequency} : Scales).length_pos (index.val + 1)
    have quotientPositive : 0 < diagonalDifference prepared.trajectory.movingFamily.patchMotion time index /
        ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 := by linarith
    exact (div_pos_iff.mp quotientPositive).resolve_right (by
      intro negative
      exact (not_lt_of_gt (sq_pos_of_pos lengthPositive)) negative.2) |>.1

end EulerNonuniqueness.Paper
