import EulerNonuniqueness.Section5.CascadeCorrectedPhaseSmallShear
import EulerNonuniqueness.Section5.CascadeCorrectedPhaseForcingContinuity
import EulerNonuniqueness.Section5.CascadeTriangularNeutralWeightedHistory
import EulerNonuniqueness.General.NonnegativeIntervalMajorant
import EulerNonuniqueness.General.WeightedTriangularFeedback

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_corrected_phase_weighted_feedback
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (coordinateZero : coordinate 0 = 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
    ∀ tolerance : ℝ, 0 < tolerance → ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
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
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 < finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∃ lift : Fin 2 → ℝ → ℝ,
      (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift side time : ℂ))) ∧
      ∀ weight : ℝ, 0 < weight →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared) index time|) ≤
        (1 + tolerance) * |changed.omega (index.val + 1)| / weight ^ 2 *
          (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
            |relativeDilationPhysicalVelocity changed first second index time|) +
        tolerance * |changed.omega (index.val + 1)| / weight *
          (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
            (|(referenceStraightenedShape first graph coordinate index time).1 -
                (referenceStraightenedShape second graph coordinate index time).1| +
              |(referenceStraightenedShape first graph coordinate index time).2 -
                (referenceStraightenedShape second graph coordinate index time).2|)) +
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
          |correctedPaperPhaseForcing changed (phaseCorrection 1 graph) first index time -
            correctedPaperPhaseForcing changed (phaseCorrection 1 graph) second index time|) / weight := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, smallShear⟩ :=
    exists_uniform_cascade_corrected_phase_small_shear graphAnalytic graphZero graphDerivative coordinateSmooth
      coordinateZero coordinateDerivative
  obtain ⟨historyRadius, historyPositive, _, history⟩ :=
    exists_uniform_cascade_triangular_neutral_weighted_history graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  obtain ⟨forcingRadius, forcingPositive, _, forcingContinuous⟩ :=
    exists_uniform_cascade_corrected_phase_forcing_continuity graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  obtain ⟨chartRadius, chartPositive, _, closedChart⟩ :=
    exists_uniform_cascade_closed_saddle_dynamics graphAnalytic.contDiffAt coordinateSmooth
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, ?_⟩
  intro tolerance tolerancePositive
  obtain ⟨shearRadius, shearPositive, shearQuarter, shear⟩ := smallShear tolerance tolerancePositive
  let radius := min shearRadius (min historyRadius (min forcingRadius (chartRadius / 2)))
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusShear : radius ≤ shearRadius := min_le_left _ _
  have radiusHistory : radius ≤ historyRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusForcing : radius ≤ forcingRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have radiusChart : radius < chartRadius :=
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (by linarith)
  refine ⟨radius, radiusPositive, radiusShear.trans shearQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative
  have thresholdEighthActual := thresholdSmall.trans thresholdEighth
  filter_upwards [shear scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorSmall
      thresholdSmall referenceNonnegative,
    history scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorPositive factorSmall
      thresholdEighthActual referenceNonnegative,
    forcingContinuous scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorPositive factorSmall
      thresholdEighthActual referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative chartPositive]
    with frequency actualShear actualHistory actualForcing referenceSmall
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishPositive finishBound small
  obtain ⟨lift, liftContinuous, polar, weighted⟩ := actualHistory prepared path index nonterminal finish finishPositive.le finishBound
    (fun time inside => (small time inside).trans radiusHistory)
  refine ⟨lift, liftContinuous, polar, ?_⟩
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let dilation := fun time => (diagonalDifference first time index - diagonalDifference second time index) /
    changed.length (index.val + 1) ^ 2
  let chartDifference := fun time => referenceStraightenedShape first graph coordinate index time -
    referenceStraightenedShape second graph coordinate index time
  let shape := fun time => |(chartDifference time).1| + |(chartDifference time).2|
  let forcing := fun time => |correctedPaperPhaseForcing changed (phaseCorrection 1 graph) first index time -
    correctedPaperPhaseForcing changed (phaseCorrection 1 graph) second index time|
  have dilationContinuous : ContinuousOn dilation (Icc 0 finish) := by
    intro time inside
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith [inside.1], by linarith [inside.2, finishBound, path.stopBound]⟩
    have derivative := ((prepared.paired_diagonal_hasDerivAt 0 index globalInside).sub
      (prepared.paired_diagonal_hasDerivAt 1 index globalInside)).div_const (changed.length (index.val + 1) ^ 2)
    exact derivative.continuousAt.continuousWithinAt
  have chartContinuous : ContinuousOn chartDifference (Icc 0 finish) := by
    intro time inside
    have pairedSmall : ∀ side,
        |unstableShape (cascadePairedMotion prepared side) time index| +
          |stableShape (cascadePairedMotion prepared side) time index| < chartRadius := by
      intro side
      fin_cases side
      · exact (small time inside).trans_lt radiusChart
      · have sharp := referenceSmall prepared time
          (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩) index
        change |unstableShape second time index| + |stableShape second time index| < chartRadius
        linarith [abs_nonneg (diagonalDifference second time index / changed.length (index.val + 1) ^ 2 - 1)]
    exact (closedChart prepared path index time ⟨inside.1, inside.2.trans finishBound⟩ pairedSmall).continuousAt.continuousWithinAt
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) := chartContinuous.fst.abs.add chartContinuous.snd.abs
  have pointForcing := actualForcing prepared path index finish finishPositive finishBound
    (fun time inside => (small time inside).trans radiusForcing)
  have forcingContinuous : ContinuousOn forcing (Icc 0 finish) := (pointForcing 0 |>.sub (pointForcing 1)).abs
  intro weight weightPositive
  have histories := weighted weight weightPositive
  let phaseShear := fun time => |relativeCorrectedPaperPhaseVelocity changed (phaseCorrection 1 graph)
    (cascadePairedMotion prepared) index time - changed.omega (index.val + 1) * dilation time|
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have majorantContinuous : ContinuousOn (fun time => Real.exp (-weight * time) *
      (tolerance * |changed.omega (index.val + 1)| * (|dilation time| + shape time) + forcing time)) (Icc 0 finish) :=
    weightContinuous.continuousOn.mul
      ((continuousOn_const.mul (dilationContinuous.abs.add shapeContinuous)).add forcingContinuous)
  have comparison := EulerNonuniqueness.General.intervalIntegral_le_of_nonnegative_majorant finishPositive.le
    (first := fun time => Real.exp (-weight * time) * phaseShear time)
    (fun time _ => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) majorantContinuous
    (fun time inside => mul_le_mul_of_nonneg_left
      (actualShear prepared path index nonterminal finish finishPositive.le finishBound
        (fun current member => (small current member).trans radiusShear) time inside) (Real.exp_pos _).le)
  have split := EulerNonuniqueness.General.weighted_integral_three_term_identity
    (weight := weight) (coefficient := tolerance * |changed.omega (index.val + 1)|)
    finishPositive.le dilationContinuous.abs shapeContinuous forcingContinuous
  rw [split] at comparison
  exact EulerNonuniqueness.General.weighted_triangular_feedback
    (abs_nonneg (changed.omega (index.val + 1))) weightPositive tolerancePositive.le histories.1 histories.2 comparison

end EulerNonuniqueness.Paper
