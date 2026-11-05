import EulerNonuniqueness.Section5.CascadeRelativeNeutralHistory

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

def relativeNormalizedFirstMoment {count : ℕ} (scales : Scales) (first second : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℂ :=
  (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) •
    (centroidAsymmetry first time index - centroidAsymmetry second time index)

theorem CascadeMaterialPreparedPair.relativeNormalizedFirstMoment_initial
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (index : Fin count) (nonterminal : index.val + 1 < count) :
    relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference index 0 = 0 := by
  simp only [relativeNormalizedFirstMoment, centroidAsymmetry,
    prepared.nonterminal_initial_centroid index nonterminal, sub_self, smul_zero]

theorem CascadeInternallyStoppedPath.relativeNormalizedFirstMoment_hasDerivAt
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) {time : ℝ} (inside : time ∈ Icc 0 path.stop) :
    HasDerivAt (relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference index)
      ((4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) •
        (quadrupoleNeutralExternalVelocity scales prepared.trajectory.movingFamily.patchMotion index time -
          quadrupoleNeutralExternalVelocity scales prepared.reference index time)) time := by
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have actual := ((prepared.paired_neutral_hasDerivAt 0 index globalInside).sub
    (prepared.paired_neutral_hasDerivAt 1 index globalInside)).const_smul
      (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2)
  rw [path.paired_neutralVelocity_eq_external amplitudePositive frequencyPositive ratioPositive 0 index inside,
    path.paired_neutralVelocity_eq_external amplitudePositive frequencyPositive ratioPositive 1 index inside] at actual
  exact actual

theorem CascadeInternallyStoppedPath.relativeNormalizedFirstMoment_original_history
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (nonterminal : index.val + 1 < count)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) :
    relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference index time =
      ∫ current in (0 : ℝ)..time,
        (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) •
          (quadrupoleNeutralExternalVelocity scales prepared.trajectory.movingFamily.patchMotion index current -
            quadrupoleNeutralExternalVelocity scales prepared.reference index current) := by
  rw [relativeNormalizedFirstMoment,
    path.relative_neutral_original_history amplitudePositive frequencyPositive ratioPositive index nonterminal inside,
    intervalIntegral.integral_smul]

theorem CascadeInternallyStoppedPath.relativeNormalizedFirstMoment_original_history_norm
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (nonterminal : index.val + 1 < count)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) :
    ‖relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖ ≤
      (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) *
        ∫ current in (0 : ℝ)..time,
          ‖quadrupoleNeutralExternalVelocity scales prepared.trajectory.movingFamily.patchMotion index current -
            quadrupoleNeutralExternalVelocity scales prepared.reference index current‖ := by
  have positive : 0 < 4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2 :=
    div_pos (mul_pos (by norm_num) (scales.location_pos _)) (sq_pos_of_pos (scales.length_pos _))
  rw [relativeNormalizedFirstMoment, norm_smul, Real.norm_eq_abs, abs_of_pos positive]
  exact mul_le_mul_of_nonneg_left
    (path.relative_neutral_original_history_norm amplitudePositive frequencyPositive ratioPositive index nonterminal inside) positive.le

end EulerNonuniqueness.Paper
