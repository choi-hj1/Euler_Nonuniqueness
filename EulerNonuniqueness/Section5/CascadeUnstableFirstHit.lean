import EulerNonuniqueness.Section5.CascadePairedChartRegularity
import EulerNonuniqueness.Section5.CascadeRelativeChartInitial
import EulerNonuniqueness.General.ContinuousPrefixBootstrap

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem exists_uniform_actual_unstable_first_hit
    {graph coordinate : ℝ → ℝ} (graphSmooth : ContDiffAt ℝ 2 graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 < count →
    ∀ horizon : ℝ, 0 ≤ horizon → horizon ≤ path.stop →
    (∀ side, ∀ time ∈ Icc 0 horizon,
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| < radius) →
    let unstable := fun time =>
      (referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time -
        referenceStraightenedShape prepared.reference graph coordinate index time).1
    ∀ level : ℝ, 0 < level → level ≤ unstable horizon →
    ∃ hit : ℝ, 0 < hit ∧ hit ≤ horizon ∧ unstable hit = level ∧
      ∀ time : ℝ, 0 ≤ time → time < hit → unstable time < level := by
  obtain ⟨radius, radiusPositive, radiusQuarter, regular⟩ :=
    exists_uniform_cascade_paired_chart_regularity graphSmooth coordinateSmooth
  refine ⟨radius, radiusPositive, radiusQuarter, ?_⟩
  intro scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor
    boundaryConstant count prepared path index nonterminal horizon horizonNonnegative horizonBound small
  dsimp only
  intro level levelPositive reached
  let unstable := fun time =>
    (referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time -
      referenceStraightenedShape prepared.reference graph coordinate index time).1
  have initial : unstable 0 = 0 := by
    have actual := prepared.nonterminal_initial_straightened_difference graph coordinate index nonterminal
    exact congrArg Prod.fst actual
  have continuous : ContinuousOn unstable (Icc 0 horizon) :=
    (regular prepared path index horizon horizonBound small).1.fst
  obtain ⟨hit, hitInside, zero, strictBefore⟩ :=
    exists_first_zero_of_initial_nonpos_of_nonnegative horizonNonnegative
      (continuous.sub continuousOn_const)
      (by simpa only [initial, zero_sub] using (neg_nonpos.mpr levelPositive.le))
      (sub_nonneg.mpr reached)
  have hitPositive : 0 < hit := by
    by_contra failure
    have atZero : hit = 0 := le_antisymm (le_of_not_gt failure) hitInside.1
    rw [atZero, initial] at zero
    linarith only [zero, levelPositive]
  refine ⟨hit, hitPositive, hitInside.2, sub_eq_zero.mp zero, ?_⟩
  intro time timeNonnegative timeBefore
  exact sub_neg.mp (strictBefore time timeNonnegative timeBefore)

end EulerNonuniqueness.Paper
