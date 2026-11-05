import EulerNonuniqueness.Section5.CascadeCenterWeightedHistory
import EulerNonuniqueness.Section5.CascadeFirstMomentSaddleWeight
import EulerNonuniqueness.Section5.CascadeCorrectedPhaseWeightedFeedback

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_neutral_weighted_budget
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
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let weight := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
      let historyIntegral := fun function : ℝ → ℝ =>
        ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
      0 < weight ∧
      (historyIntegral (fun time => ‖quadrupoleCenter first time index - quadrupoleCenter second time index‖ /
          changed.location (index.val + 1)) +
        historyIntegral (fun time => ‖relativeNormalizedFirstMoment changed first second index time‖)) +
      (historyIntegral (fun time => |(diagonalDifference first time index - diagonalDifference second time index) /
          changed.length (index.val + 1) ^ 2|) +
        historyIntegral (fun time => |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
          (cascadePairedMotion prepared) index time|)) ≤
      (historyIntegral (fun time => ‖prepared.pairedCenterVelocity 0 index time - prepared.pairedCenterVelocity 1 index time‖ /
          changed.location (index.val + 1)) / weight +
        (2 / weight) * historyIntegral (relativeFirstMomentSourceDefect changed first second index)) +
      (historyIntegral (fun time => |relativeDilationPhysicalVelocity changed first second index time|) / weight +
        ((1 + tolerance) * |changed.omega (index.val + 1)| / weight ^ 2 *
          historyIntegral (fun time => |relativeDilationPhysicalVelocity changed first second index time|) +
        tolerance * |changed.omega (index.val + 1)| / weight *
          historyIntegral (fun time =>
            |(referenceStraightenedShape first graph coordinate index time).1 -
              (referenceStraightenedShape second graph coordinate index time).1| +
            |(referenceStraightenedShape first graph coordinate index time).2 -
              (referenceStraightenedShape second graph coordinate index time).2|) +
        historyIntegral (fun time => |correctedPaperPhaseForcing changed (phaseCorrection 1 graph) first index time -
          correctedPaperPhaseForcing changed (phaseCorrection 1 graph) second index time|) / weight)) := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, feedback⟩ :=
    exists_uniform_cascade_corrected_phase_weighted_feedback graphAnalytic graphZero graphDerivative
      coordinateSmooth coordinateZero coordinateDerivative
  obtain ⟨dilationRadius, dilationPositive, _, triangular⟩ :=
    exists_uniform_cascade_triangular_neutral_weighted_history graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, ?_⟩
  intro tolerance tolerancePositive
  obtain ⟨phaseRadius, phasePositive, phaseQuarter, phaseFactory⟩ := feedback tolerance tolerancePositive
  let radius := min phaseRadius dilationRadius
  refine ⟨radius, lt_min phasePositive dilationPositive, (min_le_left _ _).trans phaseQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    phaseFactory scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorPositive
      factorSmall thresholdSmall referenceNonnegative,
    triangular scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorPositive
      factorSmall (thresholdSmall.trans thresholdEighth) referenceNonnegative,
    scales.eventually_cascade_firstMoment_weighted_source_defect amplitudePositive ratioBound alphaPositive]
    with frequency frequencyPositive phaseBound dilationBound momentBound
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishPositive finishBound small
  obtain ⟨lift, liftContinuous, polar, phaseHistory⟩ := phaseBound prepared path index nonterminal finish finishPositive
    finishBound (fun time inside => (small time inside).trans (min_le_left _ _))
  obtain ⟨_, _, _, dilationHistory⟩ := dilationBound prepared path index nonterminal finish finishPositive.le finishBound
    (fun time inside => (small time inside).trans (min_le_right _ _))
  let weight := 2 * Real.sqrt 2 * ({scales with frequency := frequency} : Scales).omega (index.val + 1)
  have weightPositive : 0 < weight := by
    dsimp only [weight]
    exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))
      (({scales with frequency := frequency} : Scales).omega_pos frequencyPositive (by change 0 < scales.ratio; linarith) _)
  refine ⟨lift, liftContinuous, polar, weightPositive, ?_⟩
  exact add_le_add
    (add_le_add (path.relative_center_weighted_history index nonterminal finishPositive.le finishBound weightPositive)
      (momentBound prepared path index nonterminal finish finishPositive.le finishBound))
    (add_le_add (dilationHistory weight weightPositive).1 (phaseHistory weight weightPositive))

end EulerNonuniqueness.Paper
