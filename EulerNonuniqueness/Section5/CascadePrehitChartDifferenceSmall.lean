import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect
import EulerNonuniqueness.Section5.CascadeInternallyStoppedPath
import EulerNonuniqueness.Section6.NormalFormForwardBound
import EulerNonuniqueness.Section6.PaperStraightenedShapeDynamics

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_prehit_chart_difference_small
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0)
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ scales : Scales, 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {referenceConstant : ℝ}, 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop, ∀ index : Fin count,
    |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius →
    |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).1 -
        (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
      |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).2 -
        (referenceStraightenedShape prepared.reference graph coordinate index time).2| ≤ tolerance := by
  obtain ⟨baseRadius, basePositive, constant, constantOne, forward⟩ :=
    localNormalFormChart_exists_uniform_forward_bound graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  have constantPositive : 0 < constant := zero_lt_one.trans_le constantOne
  let rawTolerance := min (baseRadius / 2) (tolerance / (4 * constant))
  let radius := min rawTolerance (1 / 4)
  have rawPositive : 0 < rawTolerance := by dsimp only [rawTolerance]; positivity
  have rawBase : rawTolerance < baseRadius := (min_le_left _ _).trans_lt (by linarith)
  have rawBudget : rawTolerance ≤ tolerance / (4 * constant) := min_le_right _ _
  have radiusRaw : radius ≤ rawTolerance := min_le_left _ _
  refine ⟨radius, lt_min rawPositive (by norm_num), min_le_right _ _, ?_⟩
  intro scales ratioBound alphaPositive referenceConstant referenceNonnegative
  filter_upwards [scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative rawPositive]
    with frequency referenceSmall
  intro orbit sectionTime phase dipoleAngle threshold scaleRoot shapeRadius factor monitor boundaryConstant count
    prepared path time inside index small
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  have firstRaw : |unstableShape first time index| + |stableShape first time index| < baseRadius :=
    (small.trans radiusRaw).trans_lt rawBase
  have sharp := referenceSmall prepared time ⟨inside.1, inside.2.trans path.stopBound⟩ index
  have secondRaw : |unstableShape second time index| + |stableShape second time index| < rawTolerance := by
    linarith [abs_nonneg (diagonalDifference second time index /
      ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 - 1)]
  have firstBound := forward (unstableShape first time index, stableShape first time index) firstRaw
  have secondBound := forward (unstableShape second time index, stableShape second time index) (secondRaw.trans rawBase)
  have identity : constant * (tolerance / (4 * constant)) = tolerance / 4 := by
    field_simp
    <;> ring
  have firstSize : |(referenceStraightenedShape first graph coordinate index time).1| +
      |(referenceStraightenedShape first graph coordinate index time).2| ≤ tolerance / 4 := by
    exact firstBound.trans ((mul_le_mul_of_nonneg_left ((small.trans radiusRaw).trans rawBudget) constantPositive.le).trans_eq identity)
  have secondSize : |(referenceStraightenedShape second graph coordinate index time).1| +
      |(referenceStraightenedShape second graph coordinate index time).2| ≤ tolerance / 4 := by
    exact secondBound.trans ((mul_le_mul_of_nonneg_left (secondRaw.le.trans rawBudget) constantPositive.le).trans_eq identity)
  have unstable := abs_sub
    (referenceStraightenedShape first graph coordinate index time).1
    (referenceStraightenedShape second graph coordinate index time).1
  have stable := abs_sub
    (referenceStraightenedShape first graph coordinate index time).2
    (referenceStraightenedShape second graph coordinate index time).2
  linarith

end EulerNonuniqueness.Paper
