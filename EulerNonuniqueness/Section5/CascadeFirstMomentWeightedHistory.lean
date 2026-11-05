import EulerNonuniqueness.Section5.CascadePrehitFirstMomentRate
import EulerNonuniqueness.General.TriangularNeutralWeightedHistory

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem CascadeInternallyStoppedPath.relativeNormalizedFirstMoment_weighted_history
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (nonterminal : index.val + 1 < count)
    {finish weight : ℝ} (finishNonnegative : 0 ≤ finish) (finishBound : finish ≤ path.stop)
    (weightPositive : 0 < weight) :
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        ‖relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖) ≤
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        ‖relativeFirstMomentExternalVelocity scales prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖) / weight := by
  let velocity := fun time => (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) •
    (prepared.pairedNeutralVelocity 0 index time - prepared.pairedNeutralVelocity 1 index time)
  let curve := relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference index
  have velocityContinuous : Continuous velocity :=
    ((prepared.pairedNeutralVelocity_continuous 0 index).sub
      (prepared.pairedNeutralVelocity_continuous 1 index)).const_smul _
  have derivative (time : ℝ) (inside : time ∈ Icc 0 finish) : HasDerivAt curve (velocity time) time := by
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith [inside.1], by linarith [inside.2, finishBound, path.stopBound]⟩
    exact ((prepared.paired_neutral_hasDerivAt 0 index globalInside).sub
      (prepared.paired_neutral_hasDerivAt 1 index globalInside)).const_smul _
  have curveContinuous : ContinuousOn curve (Icc 0 finish) :=
    fun time inside => (derivative time inside).continuousAt.continuousWithinAt
  have physical (time : ℝ) (inside : time ∈ Icc 0 finish) : velocity time =
      relativeFirstMomentExternalVelocity scales prepared.trajectory.movingFamily.patchMotion prepared.reference index time := by
    dsimp only [velocity, relativeFirstMomentExternalVelocity]
    rw [path.paired_neutralVelocity_eq_external amplitudePositive frequencyPositive ratioPositive 0 index
        ⟨inside.1, inside.2.trans finishBound⟩,
      path.paired_neutralVelocity_eq_external amplitudePositive frequencyPositive ratioPositive 1 index
        ⟨inside.1, inside.2.trans finishBound⟩]
    rfl
  have initial : curve 0 = 0 := prepared.relativeNormalizedFirstMoment_initial index nonterminal
  have actual := EulerNonuniqueness.General.weighted_norm_of_interior_derivative_majorant
    finishNonnegative weightPositive curveContinuous initial velocityContinuous.norm.continuousOn
    (fun _ _ => norm_nonneg _)
    (fun time inside => derivative time ⟨inside.1.le, inside.2.le⟩) (fun _ _ => le_rfl)
  have integralIdentity :
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖velocity time‖) =
        ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
          ‖relativeFirstMomentExternalVelocity scales prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖ := by
    apply intervalIntegral.integral_congr
    intro time inside
    rw [uIcc_of_le finishNonnegative] at inside
    change Real.exp (-weight * time) * ‖velocity time‖ = _
    rw [physical time inside]
  rw [integralIdentity] at actual
  exact actual

end EulerNonuniqueness.Paper
