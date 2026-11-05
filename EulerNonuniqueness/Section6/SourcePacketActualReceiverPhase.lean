import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation
import EulerNonuniqueness.Section4.ReferencePhaseKinematics

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem Scales.eventually_actual_receiver_phase_lift (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {scaleRoot boundaryConstant : ℝ} (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant shapeRadius factor monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, threshold ≤ 1 / 2 → factor ≤ 1 / 8 →
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    ∃ lift : ℝ → ℝ, Continuous lift ∧ lift 0 = phase (index.val + 1) ∧
      ∀ time ∈ Icc 0 finish,
      HasDerivAt lift (-({scales with frequency := frequency} : Scales).omega (index.val + 1) /
        referenceDilation {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion index time +
          referencePhaseError {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion index time) time ∧
      positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index =
        (‖positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index‖ : ℂ) * Complex.exp (Complex.I * (lift time : ℂ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative] with frequency frequencyOne joint
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius factor monitor count prepared path
    thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall
  let changed : Scales := {scales with frequency := frequency}
  let family := prepared.trajectory.movingFamily
  let motion := family.patchMotion
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive := changed.length_pos (index.val + 1)
  have diagonal := joint prepared path thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 finish) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, finishBound, path.stopBound]⟩
  have regularity (time : ℝ) (inside : time ∈ Icc 0 finish) :=
    (family.halfDiagonals_contDiffAt index (fun _ => globalInside time inside)).1
  have nonzero (time : ℝ) (inside : time ∈ Icc 0 finish) : positiveHalfDiagonal motion time index ≠ 0 := by
    intro zero
    have lower := (abs_le.mp (diagonal time inside).1).1
    change -(1 / 4 : ℝ) ≤ diagonalDifference motion time index / changed.length (index.val + 1) ^ 2 - 1 at lower
    have normalized : (3 / 4 : ℝ) ≤ diagonalDifference motion time index / changed.length (index.val + 1) ^ 2 := by linarith
    have multiplied := (le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp normalized
    unfold diagonalDifference at multiplied
    rw [zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at multiplied
    nlinarith [sq_pos_of_pos lengthPositive, sq_nonneg ‖negativeHalfDiagonal motion time index‖]
  have derivativeContinuous : ContinuousOn (deriv (fun time => positiveHalfDiagonal motion time index)) (Icc 0 finish) := by
    intro time inside
    have actual := ((regularity time inside).fderiv_right (m := 0) (by norm_num)).continuousAt
    exact ((ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).continuous.continuousAt.comp actual).continuousWithinAt
  have initialEquality : positiveHalfDiagonal motion 0 index =
      positiveHalfDiagonal prepared.referenceWitness.trajectory.movingFamily.patchMotion 0 index := by
    change positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion 0 index = _
    rw [← prepared.referenceIdentity]
    simp only [positiveHalfDiagonal, prepared.nonterminal_initial_centroid index nonterminal]
  have initialPolar : positiveHalfDiagonal motion 0 index = (‖positiveHalfDiagonal motion 0 index‖ : ℂ) *
      Complex.exp (Complex.I * (phase (index.val + 1) : ℂ)) := by
    rw [initialEquality, (prepared.referenceWitness.evolution.reference_initial_diagonals (by norm_num)
      amplitudePositive frequencyPositive ratioPositive prepared.referenceWitness.initial index).1]
    exact initialPositiveDiagonal_polar changed _ _ _
  obtain ⟨lift, continuous, initial, properties⟩ := General.exists_complex_phase_on_Icc finishNonnegative
    (fun time inside => (regularity time inside).differentiableAt (by norm_num) |>.hasDerivAt)
    derivativeContinuous nonzero initialPolar
  refine ⟨lift, continuous, initial, ?_⟩
  intro time inside
  have identity : -changed.omega (index.val + 1) / referenceDilation changed motion index time +
      referencePhaseError changed motion index time =
      (deriv (fun current => positiveHalfDiagonal motion current index) time / positiveHalfDiagonal motion time index).im := by
    unfold referencePhaseError
    ring
  rw [identity]
  exact properties time inside

end EulerNonuniqueness.Paper
