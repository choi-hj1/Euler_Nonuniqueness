import EulerNonuniqueness.Section5.CascadeFirstMomentWeightedHistory
import EulerNonuniqueness.General.WeightedTriangularFeedback

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

def relativeFirstMomentSourceDefect {count : ℕ} (scales : Scales) (first second : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℝ :=
  max 0 (‖relativeFirstMomentExternalVelocity scales first second index time‖ -
    (96 / Real.pi * (2304 * scales.strain)) * ‖relativeNormalizedFirstMoment scales first second index time‖)

theorem relativeFirstMomentSourceDefect_le_of_rate_bound {count : ℕ} (scales : Scales)
    (first second : PatchMotion count) (index : Fin count) (time : ℝ) {budget : ℝ}
    (budgetNonnegative : 0 ≤ budget)
    (bound : ‖relativeFirstMomentExternalVelocity scales first second index time‖ ≤
      (96 / Real.pi * (2304 * scales.strain)) * ‖relativeNormalizedFirstMoment scales first second index time‖ + budget) :
    relativeFirstMomentSourceDefect scales first second index time ≤ budget := by
  exact max_le budgetNonnegative (by linarith)

theorem CascadeInternallyStoppedPath.relativeFirstMomentExternalVelocity_continuousOn
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) :
    ContinuousOn (relativeFirstMomentExternalVelocity scales prepared.trajectory.movingFamily.patchMotion prepared.reference index)
      (Icc 0 path.stop) := by
  let velocity := fun time => (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) •
    (prepared.pairedNeutralVelocity 0 index time - prepared.pairedNeutralVelocity 1 index time)
  have velocityContinuous : Continuous velocity :=
    ((prepared.pairedNeutralVelocity_continuous 0 index).sub
      (prepared.pairedNeutralVelocity_continuous 1 index)).const_smul _
  apply velocityContinuous.continuousOn.congr
  intro time inside
  dsimp only [velocity, relativeFirstMomentExternalVelocity]
  rw [path.paired_neutralVelocity_eq_external amplitudePositive frequencyPositive ratioPositive 0 index inside,
    path.paired_neutralVelocity_eq_external amplitudePositive frequencyPositive ratioPositive 1 index inside]
  rfl

theorem CascadeInternallyStoppedPath.relativeNormalizedFirstMoment_weighted_source_defect
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (nonterminal : index.val + 1 < count)
    {finish weight : ℝ} (finishNonnegative : 0 ≤ finish) (finishBound : finish ≤ path.stop)
    (weightPositive : 0 < weight)
    (weightBound : 2 * (96 / Real.pi * (2304 * scales.strain)) ≤ weight) :
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        ‖relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖) ≤
      (2 / weight) * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        relativeFirstMomentSourceDefect scales prepared.trajectory.movingFamily.patchMotion prepared.reference index time) := by
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let curve := relativeNormalizedFirstMoment scales first second index
  let velocity := relativeFirstMomentExternalVelocity scales first second index
  let defect := relativeFirstMomentSourceDefect scales first second index
  let coefficient := 96 / Real.pi * (2304 * scales.strain)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have derivative (time : ℝ) (inside : time ∈ Icc 0 finish) : HasDerivAt curve (velocity time) time :=
    path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index (subset inside)
  have curveContinuous : ContinuousOn curve (Icc 0 finish) :=
    fun time inside => (derivative time inside).continuousAt.continuousWithinAt
  have velocityContinuous : ContinuousOn velocity (Icc 0 finish) :=
    (path.relativeFirstMomentExternalVelocity_continuousOn amplitudePositive frequencyPositive ratioPositive index).mono subset
  have defectContinuous : ContinuousOn defect (Icc 0 finish) :=
    continuous_max.comp_continuousOn
      (continuousOn_const.prodMk (velocityContinuous.norm.sub (continuousOn_const.mul curveContinuous.norm)))
  have majorantContinuous : ContinuousOn (fun time => coefficient * ‖curve time‖ + defect time) (Icc 0 finish) :=
    (continuousOn_const.mul curveContinuous.norm).add defectContinuous
  have actual := EulerNonuniqueness.General.weighted_norm_of_interior_derivative_majorant finishNonnegative weightPositive
    curveContinuous (prepared.relativeNormalizedFirstMoment_initial index nonterminal) majorantContinuous
    (fun time _ => add_nonneg (mul_nonneg coefficientNonnegative (norm_nonneg _)) (le_max_left _ _))
    (fun time inside => derivative time ⟨inside.1.le, inside.2.le⟩)
    (fun time _ => by
      have residual := le_max_right (0 : ℝ) (‖velocity time‖ - coefficient * ‖curve time‖)
      change ‖velocity time‖ ≤ coefficient * ‖curve time‖ + max 0 (‖velocity time‖ - coefficient * ‖curve time‖)
      linarith)
  have split := EulerNonuniqueness.General.weighted_integral_three_term_identity
    (first := fun time => ‖curve time‖) (second := fun _ => (0 : ℝ)) (third := defect)
    (weight := weight) (coefficient := coefficient) finishNonnegative curveContinuous.norm continuousOn_const defectContinuous
  simp only [add_zero, mul_zero, intervalIntegral.integral_zero] at split
  rw [split] at actual
  have momentNonnegative : 0 ≤ ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖curve time‖ :=
    intervalIntegral.integral_nonneg finishNonnegative fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have multiplied := (le_div_iff₀ weightPositive).mp actual
  change 2 * coefficient ≤ weight at weightBound
  have coefficientBound := mul_le_mul_of_nonneg_right weightBound momentNonnegative
  have result : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖curve time‖) ≤
      2 * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * defect time) / weight := by
    apply (le_div_iff₀ weightPositive).mpr
    nlinarith
  exact result.trans_eq (by ring)

end EulerNonuniqueness.Paper
