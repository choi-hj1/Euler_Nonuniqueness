import EulerNonuniqueness.Section5.CascadeCorrectedPhaseShearIndexRate
import EulerNonuniqueness.Section5.CascadePrehitChartDifferenceSmall
import EulerNonuniqueness.Section6.SourcePacketReceiverDiagonalSmallness
import EulerNonuniqueness.Section1.UniformReferenceIndexBudget
import EulerNonuniqueness.General.SmallPhaseShearBudget

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_corrected_phase_small_shear
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (coordinateZero : coordinate 0 = 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
    ∀ tolerance : ℝ, 0 < tolerance → ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {scaleRoot boundaryConstant factor threshold referenceConstant : ℝ},
    0 < scaleRoot → 0 ≤ boundaryConstant → factor ≤ 1 / 8 →
    threshold ≤ thresholdMax → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {shapeRadius monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∀ time ∈ Icc 0 finish,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let firstChart := referenceStraightenedShape first graph coordinate index time
    let secondChart := referenceStraightenedShape second graph coordinate index time
    let difference := |firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|
    let dilationDifference := (diagonalDifference first time index - diagonalDifference second time index) /
      changed.length (index.val + 1) ^ 2
    |relativeCorrectedPaperPhaseVelocity changed (phaseCorrection 1 graph) (cascadePairedMotion prepared) index time -
        changed.omega (index.val + 1) * dilationDifference| ≤
      tolerance * |changed.omega (index.val + 1)| * (|dilationDifference| + difference) +
      |correctedPaperPhaseForcing changed (phaseCorrection 1 graph) first index time -
        correctedPaperPhaseForcing changed (phaseCorrection 1 graph) second index time| := by
  obtain ⟨chartConstant, chartOne, constant, constantNonnegative, thresholdMax, thresholdPositive, thresholdEighth,
    baseRadius, basePositive, baseQuarter, shear⟩ :=
    exists_uniform_cascade_corrected_phase_shear_index_rate graphAnalytic graphZero graphDerivative
      coordinateSmooth coordinateZero coordinateDerivative
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, ?_⟩
  intro tolerance tolerancePositive
  let eta := min 1 (tolerance / (100 * (constant + 1)))
  have denominatorPositive : 0 < 100 * (constant + 1) := by positivity
  have etaPositive : 0 < eta := lt_min (by norm_num) (div_pos tolerancePositive denominatorPositive)
  have etaOne : eta ≤ 1 := min_le_left _ _
  have etaBudget : 100 * (constant + 1) * eta ≤ tolerance := by
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) denominatorPositive.le).trans_eq (by field_simp)
  obtain ⟨chartRadius, chartPositive, _, chartSmall⟩ :=
    exists_uniform_cascade_prehit_chart_difference_small graphAnalytic.contDiffAt coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative etaPositive
  let radius := min baseRadius chartRadius
  have radiusPositive : 0 < radius := lt_min basePositive chartPositive
  have radiusQuarter : radius ≤ 1 / 4 := (min_le_left _ _).trans baseQuarter
  refine ⟨radius, radiusPositive, radiusQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorSmall thresholdSmall referenceNonnegative
  have thresholdEighthActual : threshold ≤ 1 / 8 := thresholdSmall.trans thresholdEighth
  filter_upwards [shear scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorSmall
      thresholdSmall referenceNonnegative,
    chartSmall scales ratioBound alphaPositive referenceNonnegative,
    scales.eventually_actual_receiver_diagonal_small amplitudePositive ratioBound alphaPositive rootPositive
      boundaryNonnegative (show 0 < eta / 2 by positivity),
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative
      (show 0 < eta / 2 by positivity),
    scales.eventually_uniform_reference_index_budget_small ratioBound alphaPositive
      (mul_nonneg (zero_le_one.trans chartOne) referenceNonnegative) etaPositive,
    scales.eventually_uniform_reference_index_budget_small ratioBound alphaPositive referenceNonnegative etaPositive]
    with frequency actual chartDifference alternativeDiagonal referenceDiagonal referenceChartBudget referenceRawBudget
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound small time inside
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  let signedDilation := (diagonalDifference first time index - diagonalDifference second time index) / length ^ 2
  let dilation := |signedDilation|
  let difference := |(referenceStraightenedShape first graph coordinate index time).1 -
      (referenceStraightenedShape second graph coordinate index time).1| +
    |(referenceStraightenedShape first graph coordinate index time).2 -
      (referenceStraightenedShape second graph coordinate index time).2|
  let defect := referenceConstant * ((changed.strain + changed.strain ^ 2) / changed.omega (index.val + 1) +
    (changed.omega (index.val + 1))⁻¹ ^ 5)
  let reference := chartConstant * defect
  let forcing := |correctedPaperPhaseForcing changed (phaseCorrection 1 graph) first index time -
    correctedPaperPhaseForcing changed (phaseCorrection 1 graph) second index time|
  have rawPrefix : ∀ current ∈ Icc 0 finish,
      |unstableShape first current index| + |stableShape first current index| ≤ baseRadius :=
    fun current member => (small current member).trans (min_le_left _ _)
  have actualBound := actual prepared path index nonterminal finish finishNonnegative finishBound rawPrefix time inside
  have radial : ∀ current ∈ Icc 0 finish, |radialShape first current index| ≤ 1 / 2 := by
    intro current member
    rw [radialShape_eq_unstable_add_stable]
    exact (abs_add _ _).trans ((small current member).trans (radiusQuarter.trans (by norm_num)))
  have firstDiagonal := alternativeDiagonal prepared path (thresholdEighthActual.trans (by norm_num)) factorSmall index nonterminal
    finish finishNonnegative finishBound radial time inside
  change |diagonalDifference first time index / length ^ 2 - 1| ≤ eta / 2 at firstDiagonal
  have sharp := referenceDiagonal prepared time
    (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩) index
  have secondDiagonal : |diagonalDifference second time index / length ^ 2 - 1| ≤ eta / 2 := by
    linarith [abs_nonneg (unstableShape second time index), abs_nonneg (stableShape second time index)]
  have dilationSmall : dilation ≤ eta := by
    have identity : signedDilation = (diagonalDifference first time index / length ^ 2 - 1) -
        (diagonalDifference second time index / length ^ 2 - 1) := by dsimp only [signedDilation]; ring
    dsimp only [dilation]
    rw [identity]
    exact (abs_sub _ _).trans (by linarith)
  have differenceSmall := chartDifference prepared path time ⟨inside.1, inside.2.trans finishBound⟩ index
    ((small time inside).trans (min_le_right _ _))
  have referenceBounds : 0 ≤ reference ∧ reference < eta := by
    simpa only [reference, defect, mul_assoc] using referenceChartBudget (index.val + 1)
  have defectBounds : 0 ≤ defect ∧ defect < eta := referenceRawBudget (index.val + 1)
  have scalar := EulerNonuniqueness.General.small_phase_shear_budget
    (abs_nonneg (changed.omega (index.val + 1))) (abs_nonneg signedDilation)
    (show 0 ≤ difference by dsimp only [difference]; positivity) referenceBounds.1 defectBounds.1
    constantNonnegative etaPositive.le etaOne dilationSmall differenceSmall referenceBounds.2.le defectBounds.2.le etaBudget
  have actualScalar : |relativeCorrectedPaperPhaseVelocity changed (phaseCorrection 1 graph)
      (cascadePairedMotion prepared) index time - changed.omega (index.val + 1) * signedDilation| ≤
    4 * |changed.omega (index.val + 1)| * dilation * (2 * dilation + 3 * defect) +
      2 * |changed.omega (index.val + 1)| * constant * ((difference + 2 * reference) * difference) +
      4 * |changed.omega (index.val + 1)| * dilation * (constant * reference ^ 2) + forcing := by
    simpa only [changed, first, second, length, signedDilation, dilation, difference, reference, defect, forcing, mul_assoc]
      using actualBound
  exact actualScalar.trans (add_le_add_right scalar forcing)

end EulerNonuniqueness.Paper
