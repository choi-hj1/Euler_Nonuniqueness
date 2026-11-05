import EulerNonuniqueness.Section5.CascadeCorrectedPhaseShearRate
import EulerNonuniqueness.Section5.CascadeReferenceIndexDecay
import EulerNonuniqueness.Section5.CascadeReferenceStraightenedBound
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect
import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_corrected_phase_shear_index_rate
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (coordinateZero : coordinate 0 = 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ chartConstant ≥ (1 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
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
    let referenceDefect := referenceConstant *
      ((changed.strain + changed.strain ^ 2) / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5)
    let referenceSize := chartConstant * referenceDefect
    |relativeCorrectedPaperPhaseVelocity changed (phaseCorrection 1 graph) (cascadePairedMotion prepared) index time -
        changed.omega (index.val + 1) * dilationDifference| ≤
      4 * |changed.omega (index.val + 1)| * |dilationDifference| * (2 * |dilationDifference| + 3 * referenceDefect) +
      2 * |changed.omega (index.val + 1)| * constant * ((difference + 2 * referenceSize) * difference) +
      4 * |changed.omega (index.val + 1)| * |dilationDifference| * (constant * referenceSize ^ 2) +
      |correctedPaperPhaseForcing changed (phaseCorrection 1 graph) first index time -
        correctedPaperPhaseForcing changed (phaseCorrection 1 graph) second index time| := by
  obtain ⟨constant, constantNonnegative, baseRadius, basePositive, phaseBound⟩ :=
    sameGraph_relativeCorrectedPhaseVelocity_exists_shear_bound graphAnalytic graphZero graphDerivative
      coordinateSmooth coordinateZero coordinateDerivative
  obtain ⟨baseThreshold, thresholdPositive, chartConstant, chartOne, chartBound⟩ :=
    exists_uniform_cascade_reference_straightened_bound graphAnalytic.contDiffAt coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  let thresholdMax := min baseThreshold (1 / 8)
  let radius := min (baseRadius / 2) (1 / 4)
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusQuarter : radius ≤ 1 / 4 := min_le_right _ _
  have radiusBase : radius < baseRadius := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨chartConstant, chartOne, constant, constantNonnegative, thresholdMax,
    lt_min thresholdPositive (by norm_num), min_le_right _ _, radius, radiusPositive, radiusQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorSmall thresholdSmall referenceNonnegative
  have thresholdEighth : threshold ≤ 1 / 8 := thresholdSmall.trans (min_le_right _ _)
  have thresholdBase : threshold ≤ baseThreshold := thresholdSmall.trans (min_le_left _ _)
  filter_upwards [scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative basePositive]
    with frequency joint referenceSmall
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound small time inside
  let changed : Scales := {scales with frequency := frequency}
  let length := changed.length (index.val + 1)
  have lengthPositive : 0 < length := changed.length_pos _
  have radial : ∀ current ∈ Icc 0 finish,
      |radialShape prepared.trajectory.movingFamily.patchMotion current index| ≤ 1 / 2 := by
    intro current member
    rw [radialShape_eq_unstable_add_stable]
    exact (abs_add _ _).trans ((small current member).trans (radiusQuarter.trans (by norm_num)))
  have diagonal := (joint prepared path (thresholdEighth.trans (by norm_num)) factorSmall index nonterminal finish
    finishNonnegative finishBound radial time inside).1
  have firstLower : length ^ 2 / 2 ≤ diagonalDifference prepared.trajectory.movingFamily.patchMotion time index := by
    have negative := neg_abs_le (diagonalDifference prepared.trajectory.movingFamily.patchMotion time index / length ^ 2 - 1)
    have lower : (3 / 4 : ℝ) ≤ diagonalDifference prepared.trajectory.movingFamily.patchMotion time index / length ^ 2 := by
      change |diagonalDifference prepared.trajectory.movingFamily.patchMotion time index / length ^ 2 - 1| ≤ 1 / 4 at diagonal
      linarith
    nlinarith [(le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp lower]
  obtain ⟨_, _, _, _, _, coarse, _⟩ := prepared.referenceSolution
  have secondLower : length ^ 2 / 2 ≤ diagonalDifference prepared.reference time index := by
    have lower := (coarse.2.1 time
      ⟨inside.1, by linarith [inside.2, finishBound, path.stopBound]⟩ index).2.2.1
    change (1 / 2 : ℝ) ≤ diagonalDifference prepared.reference time index / length ^ 2 at lower
    nlinarith [(le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp lower]
  have secondUpper : diagonalDifference prepared.reference time index ≤ 2 * length ^ 2 := by
    have upper := (coarse.2.1 time
      ⟨inside.1, by linarith [inside.2, finishBound, path.stopBound]⟩ index).2.2.2.1
    change diagonalDifference prepared.reference time index / length ^ 2 ≤ 2 at upper
    exact (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mp upper
  have pairedSmall : ∀ side,
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| < baseRadius := by
    intro side
    fin_cases side
    · exact (small time inside).trans_lt radiusBase
    · have sharp := referenceSmall prepared time
        (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩) index
      change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < baseRadius
      linarith [abs_nonneg (diagonalDifference prepared.reference time index / length ^ 2 - 1)]
  have lower : ∀ side, length ^ 2 / 2 ≤ diagonalDifference (cascadePairedMotion prepared side) time index := by
    intro side
    fin_cases side
    · exact firstLower
    · exact secondLower
  have actualReference := chartBound prepared path thresholdBase time ⟨inside.1, inside.2.trans finishBound⟩ index
  have actual := phaseBound changed (cascadePairedMotion prepared) index time pairedSmall lower secondUpper _ actualReference
  have sharp := prepared.reference_sharp_defect_le_index_budget
    (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩) index
  have defectBound : |diagonalDifference prepared.reference time index / length ^ 2 - 1| ≤
      referenceConstant * ((changed.strain + changed.strain ^ 2) / changed.omega (index.val + 1) +
        (changed.omega (index.val + 1))⁻¹ ^ 5) := by
    linarith [abs_nonneg (unstableShape prepared.reference time index), abs_nonneg (stableShape prepared.reference time index)]
  dsimp only at actual ⊢
  have firstMotion : cascadePairedMotion prepared (0 : Fin 2) = prepared.trajectory.movingFamily.patchMotion := rfl
  have secondMotion : cascadePairedMotion prepared (1 : Fin 2) = prepared.reference := rfl
  simp only [firstMotion, secondMotion] at actual
  simp only [mul_assoc] at actual ⊢
  apply actual.trans
  gcongr

end EulerNonuniqueness.Paper
