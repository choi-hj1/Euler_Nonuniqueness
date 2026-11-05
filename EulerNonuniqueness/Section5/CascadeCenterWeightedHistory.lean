import EulerNonuniqueness.Section5.CascadeRelativeCenterHistory
import EulerNonuniqueness.General.TriangularNeutralWeightedHistory

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem CascadeInternallyStoppedPath.relative_center_weighted_history
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared) (index : Fin count) (nonterminal : index.val + 1 < count)
    {finish weight : ℝ} (finishNonnegative : 0 ≤ finish) (finishBound : finish ≤ path.stop)
    (weightPositive : 0 < weight) :
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        (‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index -
          quadrupoleCenter prepared.reference time index‖ / scales.location (index.val + 1))) ≤
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        (‖prepared.pairedCenterVelocity 0 index time - prepared.pairedCenterVelocity 1 index time‖ /
          scales.location (index.val + 1))) / weight := by
  let normalization := (scales.location (index.val + 1))⁻¹
  let curve := fun time => normalization •
    (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index -
      quadrupoleCenter prepared.reference time index)
  let velocity := fun time => normalization •
    (prepared.pairedCenterVelocity 0 index time - prepared.pairedCenterVelocity 1 index time)
  have normalizationNonnegative : 0 ≤ normalization := inv_nonneg.mpr (scales.location_pos _).le
  have velocityContinuous : Continuous velocity :=
    ((prepared.pairedCenterVelocity_continuous 0 index).sub
      (prepared.pairedCenterVelocity_continuous 1 index)).const_smul _
  have derivative (time : ℝ) (inside : time ∈ Icc 0 finish) : HasDerivAt curve (velocity time) time := by
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith [inside.1], by linarith [inside.2, finishBound, path.stopBound]⟩
    exact ((prepared.paired_center_hasDerivAt 0 index globalInside).sub
      (prepared.paired_center_hasDerivAt 1 index globalInside)).const_smul _
  have curveContinuous : ContinuousOn curve (Icc 0 finish) :=
    fun time inside => (derivative time inside).continuousAt.continuousWithinAt
  have initial : curve 0 = 0 := by
    dsimp only [curve]
    rw [prepared.nonterminal_initial_center index nonterminal, sub_self, smul_zero]
  have actual := EulerNonuniqueness.General.weighted_norm_of_interior_derivative_majorant
    finishNonnegative weightPositive curveContinuous initial velocityContinuous.norm.continuousOn
    (fun _ _ => norm_nonneg _)
    (fun time inside => derivative time ⟨inside.1.le, inside.2.le⟩) (fun _ _ => le_rfl)
  simpa only [curve, velocity, norm_smul, Real.norm_eq_abs, abs_of_nonneg normalizationNonnegative,
    normalization, div_eq_mul_inv, mul_comm (scales.location (index.val + 1))⁻¹] using actual

end EulerNonuniqueness.Paper
