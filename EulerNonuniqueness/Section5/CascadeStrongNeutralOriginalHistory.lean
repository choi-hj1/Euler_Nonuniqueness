import EulerNonuniqueness.Section5.CascadeStrongNeutralReconstruction
import EulerNonuniqueness.Section5.CascadeCorrectedPhaseOriginalHistory

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_strong_neutral_original_history
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {scaleRoot boundaryConstant factor threshold referenceConstant : ℝ},
    0 < scaleRoot → 0 ≤ boundaryConstant → 0 < factor → factor ≤ 1 / 8 →
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
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
    ∃ lift : Fin 2 → ℝ → ℝ,
      (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift side time : ℂ))) ∧
      (∀ time ∈ Icc 0 finish,
        relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared) index time =
          ∫ current in (0 : ℝ)..time,
            relativeCorrectedPaperPhaseVelocity {scales with frequency := frequency} (phaseCorrection 1 graph)
              (cascadePairedMotion prepared) index current) ∧
      ∀ time ∈ Icc 0 finish,
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / changed.length (index.val + 1) ≤
        (changed.length (index.val + 1) / (4 * changed.location (index.val + 1))) *
          ‖relativeNormalizedFirstMoment changed first second index time‖ +
        constant * (|diagonalDifference first time index - diagonalDifference second time index| / changed.length (index.val + 1) ^ 2 +
          |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
          |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2| +
          |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared) index time|) := by
  obtain ⟨correctionSmooth, _, _, _, _, _, _, _⟩ :=
    sameGraph_phaseCorrection_exists_uniform_stable_factor graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  obtain ⟨reconstructionRadius, reconstructionPositive, reconstructionQuarter, constant, constantOne, reconstruction⟩ :=
    exists_uniform_cascade_strong_neutral_reconstruction graphAnalytic.contDiffAt
      coordinateSmooth (correctionSmooth.of_le (by norm_num)) graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨historyRadius, historyPositive, _, history⟩ :=
    exists_uniform_cascade_sameGraph_corrected_phase_original_history graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  let radius := min reconstructionRadius (historyRadius / 2)
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusReconstruction : radius ≤ reconstructionRadius := min_le_left _ _
  have radiusHistory : radius < historyRadius :=
    (min_le_right _ _).trans_lt (by linarith)
  have radiusQuarter : radius ≤ 1 / 4 := radiusReconstruction.trans reconstructionQuarter
  refine ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative
  filter_upwards [reconstruction scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      thresholdSmall referenceNonnegative,
    history scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorPositive factorSmall
      thresholdSmall referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative historyPositive]
    with frequency reconstruct actualHistory referenceSmall
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound small
  have radial : ∀ time ∈ Icc 0 finish,
      |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2 := by
    intro time inside
    have identity : radialShape prepared.trajectory.movingFamily.patchMotion time index =
        unstableShape prepared.trajectory.movingFamily.patchMotion time index +
          stableShape prepared.trajectory.movingFamily.patchMotion time index := by
      unfold unstableShape stableShape
      ring
    rw [identity]
    exact (abs_add_le _ _).trans ((small time inside).trans (radiusQuarter.trans (by norm_num)))
  have pairedSmall : ∀ side, ∀ time ∈ Icc 0 finish,
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| < historyRadius := by
    intro side time inside
    fin_cases side
    · exact (small time inside).trans_lt radiusHistory
    · have actual := referenceSmall prepared time
        (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩) index
      change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < historyRadius
      linarith [abs_nonneg (diagonalDifference prepared.reference time index /
        ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 - 1)]
  obtain ⟨lift, continuous, polar, integral⟩ :=
    actualHistory prepared path index nonterminal finish finishNonnegative finishBound pairedSmall
  refine ⟨lift, continuous, polar, integral, ?_⟩
  intro time inside
  have actual := reconstruct prepared path factorSmall index nonterminal finish finishNonnegative finishBound radial time inside
    ((small time inside).trans radiusReconstruction) (lift 0) (lift 1) (polar 0 time inside) (polar 1 time inside)
  exact actual

end EulerNonuniqueness.Paper
