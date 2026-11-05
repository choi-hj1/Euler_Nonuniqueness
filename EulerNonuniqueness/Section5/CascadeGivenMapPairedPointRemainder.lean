import EulerNonuniqueness.Section6.GivenMapPairedSaddleRemainder
import EulerNonuniqueness.Section5.CascadeSaddlePointRemainder
import EulerNonuniqueness.Section5.CascadeReferenceStraightenedBound
import EulerNonuniqueness.Section5.CascadeReferenceIndexDecay
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000

theorem exists_uniform_actual_given_map_paired_point_remainder
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ chartConstant ≥ (1 : ℝ), ∃ constant ≥ (1 : ℝ),
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {scaleRoot boundaryConstant factor threshold referenceConstant : ℝ},
    0 < scaleRoot → 0 ≤ boundaryConstant → 0 < factor → factor ≤ 1 / 8 →
    threshold ≤ thresholdMax → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {shapeRadius monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∀ time ∈ Icc 0 finish,
    let changed : Scales := {scales with frequency := frequency}
    let first := referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time
    let second := referenceStraightenedShape prepared.reference graph coordinate index time
    let shape := |first.1 - second.1| + |first.2 - second.2|
    let dilation := |diagonalDifference prepared.trajectory.movingFamily.patchMotion time index -
      diagonalDifference prepared.reference time index| / changed.length (index.val + 1) ^ 2
    let referenceSize := chartConstant * referenceConstant *
      ((changed.strain + changed.strain ^ 2) / changed.omega (index.val + 1) +
        (changed.omega (index.val + 1))⁻¹ ^ 5)
    ‖relativeStraightenedSaddlePointRemainder changed (cascadePairedMotion prepared) graph coordinate index time‖ ≤
      constant * |changed.omega (index.val + 1)| *
        ((shape + dilation + referenceSize) * shape + referenceSize * dilation) := by
  obtain ⟨pointRadius, pointPositive, constant, constantOne, point⟩ :=
    givenMap_paired_saddle_remainder_bound graphSmooth coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨referenceThreshold, referenceThresholdPositive, referenceChartConstant, referenceChartOne, referenceCharts⟩ :=
    exists_uniform_cascade_reference_straightened_bound graphSmooth coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  let chartConstant := referenceChartConstant + 1
  let thresholdMax := min referenceThreshold (1 / 8)
  let radius := min (pointRadius / 2) (1 / 4)
  have chartOne : 1 ≤ chartConstant := by dsimp only [chartConstant]; linarith only [referenceChartOne]
  refine ⟨chartConstant, chartOne, constant, constantOne, thresholdMax,
    lt_min referenceThresholdPositive (by norm_num), min_le_right _ _, radius,
    lt_min (half_pos pointPositive) (by norm_num), min_le_right _ _, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdBound referenceNonnegative
  filter_upwards [scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative pointPositive]
    with frequency joint referenceSmall
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound chartSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let length := changed.length (index.val + 1)
  let firstDilation := diagonalDifference motion time index / length ^ 2
  let secondDilation := diagonalDifference prepared.reference time index / length ^ 2
  let firstChart := referenceStraightenedShape motion graph coordinate index time
  let secondChart := referenceStraightenedShape prepared.reference graph coordinate index time
  let shape := |firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|
  let dilation := |diagonalDifference motion time index - diagonalDifference prepared.reference time index| / length ^ 2
  let rawBudget := referenceConstant * ((changed.strain + changed.strain ^ 2) / changed.omega (index.val + 1) +
    (changed.omega (index.val + 1))⁻¹ ^ 5)
  let referenceSize := chartConstant * rawBudget
  let referenceDefect := |secondDilation - 1|
  let referenceChartSize := |secondChart.1| + |secondChart.2|
  have stoppedInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have unitInside : time ∈ Icc (0 : ℝ) 1 := ⟨inside.1, stoppedInside.2.trans path.stopBound⟩
  have radialSmall (current : ℝ) (currentInside : current ∈ Icc 0 finish) :
      |radialShape motion current index| ≤ 1 / 2 := by
    rw [radialShape_eq_unstable_add_stable]
    exact (abs_add _ _).trans ((chartSmall current currentInside).trans
      ((min_le_right _ _).trans (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)))
  have diagonal := joint prepared path
    (thresholdBound.trans ((min_le_right _ _).trans (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2)))
    factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have firstLower : (1 / 2 : ℝ) ≤ firstDilation := by
    have lower := (abs_le.mp diagonal.1).1
    change -(1 / 4 : ℝ) ≤ firstDilation - 1 at lower
    linarith only [lower]
  obtain ⟨_, _, _, _, _, coarse, _⟩ := prepared.referenceSolution
  have secondLower : (1 / 2 : ℝ) ≤ secondDilation :=
    (coarse.2.1 time ⟨inside.1, (unitInside.2.trans (by norm_num : (1 : ℝ) ≤ 2))⟩ index).2.2.1
  have firstSmall : |unstableShape motion time index| + |stableShape motion time index| < pointRadius := by
    have bounded := (chartSmall time inside).trans (min_le_left _ _)
    linarith only [bounded, pointPositive]
  have secondSmall : |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < pointRadius := by
    have actual := referenceSmall prepared time unitInside index
    have defectNonnegative := abs_nonneg (secondDilation - 1)
    linarith only [actual, defectNonnegative]
  have actual := point (changed.omega (index.val + 1)) firstDilation secondDilation
    (unstableShape motion time index, stableShape motion time index)
    (unstableShape prepared.reference time index, stableShape prepared.reference time index)
    firstSmall secondSmall firstLower secondLower
  change ‖relativeStraightenedSaddlePointRemainder changed (cascadePairedMotion prepared) graph coordinate index time‖ ≤
    constant * |changed.omega (index.val + 1)| *
      ((shape + referenceChartSize + |firstDilation - 1|) * shape +
        |firstDilation - secondDilation| * referenceChartSize) at actual
  have sharp := prepared.reference_sharp_defect_le_index_budget unitInside index
  change referenceDefect + |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| ≤ rawBudget at sharp
  have rawNonnegative : 0 ≤ rawBudget :=
    (by dsimp only [referenceDefect]; positivity :
      0 ≤ referenceDefect + |unstableShape prepared.reference time index| + |stableShape prepared.reference time index|).trans sharp
  have defectBound : referenceDefect ≤ rawBudget := by
    linarith only [sharp, abs_nonneg (unstableShape prepared.reference time index), abs_nonneg (stableShape prepared.reference time index)]
  have chartBound : referenceChartSize ≤ referenceChartConstant * rawBudget := by
    simpa only [referenceChartSize, secondChart, rawBudget, mul_assoc] using
      referenceCharts prepared path (thresholdBound.trans (min_le_left _ _)) time stoppedInside index
  have combined : referenceChartSize + referenceDefect ≤ referenceSize := by
    have summed := add_le_add chartBound defectBound
    dsimp only [referenceSize, chartConstant]
    nlinarith only [summed]
  have referenceBound : referenceChartSize ≤ referenceSize :=
    (le_add_of_nonneg_right (abs_nonneg _)).trans combined
  have differenceIdentity : |firstDilation - secondDilation| = dilation := by
    dsimp only [firstDilation, secondDilation, dilation]
    rw [← sub_div, abs_div, abs_of_pos (sq_pos_of_pos (changed.length_pos _))]
  have firstDefect : |firstDilation - 1| ≤ dilation + referenceDefect := by
    have identity : firstDilation - 1 = (firstDilation - secondDilation) + (secondDilation - 1) := by ring
    rw [identity]
    exact (abs_add _ _).trans_eq (by rw [differenceIdentity])
  have shapeNonnegative : 0 ≤ shape := by dsimp only [shape]; positivity
  have differenceNonnegative : 0 ≤ dilation := div_nonneg (abs_nonneg _) (sq_nonneg _)
  have firstBound : (shape + referenceChartSize + |firstDilation - 1|) * shape ≤
      (shape + dilation + referenceSize) * shape :=
    mul_le_mul_of_nonneg_right (by linarith only [combined, firstDefect]) shapeNonnegative
  have secondBound : |firstDilation - secondDilation| * referenceChartSize ≤ dilation * referenceSize := by
    rw [differenceIdentity]
    exact mul_le_mul_of_nonneg_left referenceBound differenceNonnegative
  apply actual.trans
  have bound := mul_le_mul_of_nonneg_left (add_le_add firstBound secondBound)
    (mul_nonneg (zero_le_one.trans constantOne) (abs_nonneg (changed.omega (index.val + 1))))
  convert bound using 1
  dsimp only [shape, firstChart, secondChart, dilation, length, referenceSize, rawBudget]
  ring

end EulerNonuniqueness.Paper

