import EulerNonuniqueness.Section5.CascadeFirstMomentSourceDefect
import EulerNonuniqueness.Section1.UniformFirstMomentWeight

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem Scales.eventually_cascade_firstMoment_arbitrary_weight_source_defect (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) :
    ∀ᶠ frequency : ℝ in atTop,
    let changed : Scales := {scales with frequency := frequency}
    (∀ index : ℕ, 1 ≤ changed.omega index ∧
      2 * (96 / Real.pi * (2304 * changed.strain)) ≤ changed.omega index) ∧
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair changed orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    ∀ weight : ℝ, changed.omega (index.val + 1) ≤ weight →
    IntervalIntegrable (fun time => Real.exp (-weight * time) *
      ‖relativeNormalizedFirstMoment changed prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖)
        volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) *
      relativeFirstMomentSourceDefect changed prepared.trajectory.movingFamily.patchMotion prepared.reference index time)
        volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        ‖relativeNormalizedFirstMoment changed prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖) ≤
      (2 / weight) * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        relativeFirstMomentSourceDefect changed prepared.trajectory.movingFamily.patchMotion prepared.reference index time) := by
  let coefficient := 96 / Real.pi * 2304
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  filter_upwards [eventually_ge_atTop (max 1 (2 * coefficient)),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyLarge strainSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have frequencyOne : 1 ≤ frequency := (le_max_left _ _).trans frequencyLarge
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have uniformWeights (index : ℕ) : 1 ≤ changed.omega index ∧
      2 * (96 / Real.pi * (2304 * changed.strain)) ≤ changed.omega index := by
    have frequencyOmega := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) index
    have driftBound : 96 / Real.pi * (2304 * changed.strain) ≤ coefficient := by
      simpa only [coefficient, mul_assoc, mul_one] using
        mul_le_mul_of_nonneg_left strainSmall.le coefficientNonnegative
    refine ⟨frequencyOne.trans frequencyOmega, ?_⟩
    exact (mul_le_mul_of_nonneg_left driftBound (by norm_num : (0 : ℝ) ≤ 2)).trans
      (((le_max_right _ _).trans frequencyLarge).trans frequencyOmega)
  refine ⟨uniformWeights, ?_⟩
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count
    prepared path index nonterminal finish finishNonnegative finishBound weight weightBound
  have weightPositive : 0 < weight := (zero_lt_one.trans_le (uniformWeights (index.val + 1)).1).trans_le weightBound
  have driftWeight := (uniformWeights (index.val + 1)).2.trans weightBound
  let curve := relativeNormalizedFirstMoment changed prepared.trajectory.movingFamily.patchMotion prepared.reference index
  let velocity := relativeFirstMomentExternalVelocity changed prepared.trajectory.movingFamily.patchMotion prepared.reference index
  let defect := relativeFirstMomentSourceDefect changed prepared.trajectory.movingFamily.patchMotion prepared.reference index
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have curveContinuous : ContinuousOn curve (Icc 0 finish) := fun time inside =>
    (path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index
      (subset inside)).continuousAt.continuousWithinAt
  have velocityContinuous : ContinuousOn velocity (Icc 0 finish) :=
    (path.relativeFirstMomentExternalVelocity_continuousOn amplitudePositive frequencyPositive ratioPositive index).mono subset
  have defectContinuous : ContinuousOn defect (Icc 0 finish) :=
    continuous_max.comp_continuousOn (continuousOn_const.prodMk
      (velocityContinuous.norm.sub (continuousOn_const.mul curveContinuous.norm)))
  have exponential : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  refine ⟨(exponential.continuousOn.mul curveContinuous.norm).intervalIntegrable_of_Icc finishNonnegative,
    (exponential.continuousOn.mul defectContinuous).intervalIntegrable_of_Icc finishNonnegative, ?_⟩
  exact path.relativeNormalizedFirstMoment_weighted_source_defect amplitudePositive frequencyPositive ratioPositive index
    nonterminal finishNonnegative finishBound weightPositive driftWeight

end EulerNonuniqueness.Paper
