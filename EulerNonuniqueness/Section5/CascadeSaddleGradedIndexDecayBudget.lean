import EulerNonuniqueness.Section5.CascadeSaddleReferenceSplit
import EulerNonuniqueness.Section5.CascadeReferenceIndexDecay
import EulerNonuniqueness.Section5.CascadeReferenceStraightenedBound
import EulerNonuniqueness.General.ReferenceDecayGradedSaddleBudget

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem exists_uniform_cascade_saddle_graded_index_decay_budget
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), ∃ chartConstant ≥ (1 : ℝ),
    ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, threshold ≤ thresholdMax →
    ∀ time ∈ Icc 0 path.stop, ∀ index : Fin count,
    ∀ pointConstant errorConstant : ℝ, 0 ≤ pointConstant → 0 ≤ errorConstant →
    let first := referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time
    let second := referenceStraightenedShape prepared.reference graph coordinate index time
    let difference := |first.1 - second.1| + |first.2 - second.2|
    let dilationDifference := |diagonalDifference prepared.trajectory.movingFamily.patchMotion time index -
      diagonalDifference prepared.reference time index| / scales.length (index.val + 1) ^ 2
    let referenceSize := chartConstant * referenceConstant *
      ((scales.strain + scales.strain ^ 2) / scales.omega (index.val + 1) +
        (scales.omega (index.val + 1))⁻¹ ^ 5)
    relativeStraightenedSaddlePointBudget scales (cascadePairedMotion prepared) graph coordinate
        pointConstant errorConstant index time ≤
      (1 + 12 * Real.sqrt 2 + 4 * pointConstant + 4 * errorConstant) * |scales.omega (index.val + 1)| *
        ((referenceSize + dilationDifference + |first.2 - second.2|) * difference + referenceSize * dilationDifference) := by
  obtain ⟨thresholdMax, thresholdPositive, chartConstant, chartOne, chartBound⟩ :=
    exists_uniform_cascade_reference_straightened_bound graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  refine ⟨thresholdMax, thresholdPositive, chartConstant, chartOne, ?_⟩
  intro scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor
    boundaryConstant count prepared path thresholdSmall time inside index pointConstant errorConstant pointNonnegative errorNonnegative
  dsimp only
  let first := referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time
  let second := referenceStraightenedShape prepared.reference graph coordinate index time
  let difference := |first.1 - second.1| + |first.2 - second.2|
  let dilationDifference := |diagonalDifference prepared.trajectory.movingFamily.patchMotion time index -
    diagonalDifference prepared.reference time index| / scales.length (index.val + 1) ^ 2
  let referenceDefect := |diagonalDifference prepared.reference time index / scales.length (index.val + 1) ^ 2 - 1|
  let rawBudget := referenceConstant * ((scales.strain + scales.strain ^ 2) / scales.omega (index.val + 1) +
    (scales.omega (index.val + 1))⁻¹ ^ 5)
  let referenceSize := chartConstant * rawBudget
  have sharp := prepared.reference_sharp_defect_le_index_budget
    (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1, inside.2.trans path.stopBound⟩) index
  have rawNonnegative : 0 ≤ rawBudget := by
    change referenceDefect + |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| ≤ rawBudget at sharp
    exact (by positivity : 0 ≤ referenceDefect + |unstableShape prepared.reference time index| +
      |stableShape prepared.reference time index|).trans sharp
  have referenceNonnegative : 0 ≤ referenceSize := mul_nonneg (zero_le_one.trans chartOne) rawNonnegative
  have defectBound : referenceDefect ≤ referenceSize := by
    have rawBound : referenceDefect ≤ rawBudget := by
      change referenceDefect + |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| ≤ rawBudget at sharp
      linarith [abs_nonneg (unstableShape prepared.reference time index), abs_nonneg (stableShape prepared.reference time index)]
    have enlarged : rawBudget ≤ chartConstant * rawBudget := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right chartOne rawNonnegative
    exact rawBound.trans enlarged
  have sizeBound : |second.1| + |second.2| ≤ referenceSize := by
    simpa only [second, referenceSize, rawBudget, mul_assoc] using chartBound prepared path thresholdSmall time inside index
  have comparison := relativeStraightenedSaddlePointBudget_le_reference_split scales (cascadePairedMotion prepared)
    graph coordinate pointConstant errorConstant index time
  dsimp only [cascadePairedMotion, Fin.cases_zero, Fin.cases_succ] at comparison
  have enlarged : relativeStraightenedSaddlePointBudget scales (cascadePairedMotion prepared) graph coordinate
      pointConstant errorConstant index time ≤
    2 * Real.sqrt 2 * (2 * |scales.omega (index.val + 1)| * (referenceSize + dilationDifference) * difference +
      4 * |scales.omega (index.val + 1)| * dilationDifference * referenceSize) +
    2 * |scales.omega (index.val + 1)| * (pointConstant * difference * (|first.2 - second.2| + referenceSize)) +
      (4 * |scales.omega (index.val + 1)| * dilationDifference) * (errorConstant * referenceSize) := by
    apply comparison.trans
    change 2 * Real.sqrt 2 * (2 * |scales.omega (index.val + 1)| * (referenceDefect + dilationDifference) * difference +
      4 * |scales.omega (index.val + 1)| * dilationDifference * (|second.1| + |second.2|)) +
      2 * |scales.omega (index.val + 1)| * (pointConstant * difference * (|first.2 - second.2| + |second.1| + |second.2|)) +
      (4 * |scales.omega (index.val + 1)| * dilationDifference) * (errorConstant * (|second.1| + |second.2|)) ≤ _
    have grouped : |first.2 - second.2| + |second.1| + |second.2| ≤ |first.2 - second.2| + referenceSize := by linarith
    gcongr
  have scalar := EulerNonuniqueness.General.reference_decay_graded_saddle_budget
    (abs_nonneg (scales.omega (index.val + 1))) referenceNonnegative
    (show 0 ≤ difference by dsimp only [difference]; positivity)
    (show 0 ≤ dilationDifference by dsimp only [dilationDifference]; positivity)
    (abs_nonneg (first.2 - second.2))
    pointNonnegative errorNonnegative
  exact enlarged.trans (by simpa only [referenceSize, rawBudget, mul_assoc] using scalar)

end EulerNonuniqueness.Paper
