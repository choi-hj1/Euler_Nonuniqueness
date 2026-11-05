import EulerNonuniqueness.Section5.CascadeStrongNeutralSplitReconstruction
import EulerNonuniqueness.Section5.CascadeNeutralWeightedBudget

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

namespace CascadeMaterialPreparedPair

def neutralWeightedSourceBudget
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (graph coordinate : ℝ → ℝ) (tolerance : ℝ) (index : Fin count) (finish : ℝ) : ℝ :=
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let weight := 2 * Real.sqrt 2 * scales.omega (index.val + 1)
  let historyIntegral := fun function : ℝ → ℝ =>
    ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  (historyIntegral (fun time => ‖prepared.pairedCenterVelocity 0 index time - prepared.pairedCenterVelocity 1 index time‖ /
      scales.location (index.val + 1)) / weight +
    (2 / weight) * historyIntegral (relativeFirstMomentSourceDefect scales first second index)) +
  (historyIntegral (fun time => |relativeDilationPhysicalVelocity scales first second index time|) / weight +
    ((1 + tolerance) * |scales.omega (index.val + 1)| / weight ^ 2 *
      historyIntegral (fun time => |relativeDilationPhysicalVelocity scales first second index time|) +
    tolerance * |scales.omega (index.val + 1)| / weight *
      historyIntegral (fun time =>
        |(referenceStraightenedShape first graph coordinate index time).1 -
          (referenceStraightenedShape second graph coordinate index time).1| +
        |(referenceStraightenedShape first graph coordinate index time).2 -
          (referenceStraightenedShape second graph coordinate index time).2|) +
    historyIntegral (fun time => |correctedPaperPhaseForcing scales (phaseCorrection 1 graph) first index time -
      correctedPaperPhaseForcing scales (phaseCorrection 1 graph) second index time|) / weight))

end CascadeMaterialPreparedPair

theorem exists_uniform_cascade_comoving_weighted_source_budget
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (coordinateZero : coordinate 0 = 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ constant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
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
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let weight := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
    let historyIntegral := fun function : ℝ → ℝ =>
      ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
    historyIntegral (fun time =>
      ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
          changed.length (index.val + 1)) ≤
      constant * (prepared.neutralWeightedSourceBudget graph coordinate tolerance index finish +
        historyIntegral (fun time =>
          |(referenceStraightenedShape first graph coordinate index time).1 -
            (referenceStraightenedShape second graph coordinate index time).1| +
          |(referenceStraightenedShape first graph coordinate index time).2 -
            (referenceStraightenedShape second graph coordinate index time).2|)) := by
  obtain ⟨reconstructionRadius, reconstructionPositive, reconstructionQuarter, constant, constantOne, reconstruction⟩ :=
    exists_uniform_cascade_strong_neutral_split_reconstruction graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, neutral⟩ :=
    exists_uniform_cascade_neutral_weighted_budget graphAnalytic graphZero graphDerivative coordinateSmooth
      coordinateZero coordinateDerivative
  refine ⟨constant, constantOne, thresholdMax, thresholdPositive, thresholdEighth, ?_⟩
  intro tolerance tolerancePositive
  obtain ⟨neutralRadius, neutralPositive, _, neutralFactory⟩ := neutral tolerance tolerancePositive
  let radius := min reconstructionRadius neutralRadius
  refine ⟨radius, lt_min reconstructionPositive neutralPositive,
    (min_le_left _ _).trans reconstructionQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative
  filter_upwards [reconstruction scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorSmall
      (thresholdSmall.trans thresholdEighth) referenceNonnegative,
    neutralFactory scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorPositive
      factorSmall thresholdSmall referenceNonnegative,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1)]
    with frequency reconstruct neutralBound lengths
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishPositive finishBound small
  obtain ⟨lift, liftContinuous, polar, _, actualNeutral⟩ := neutralBound prepared path index nonterminal finish finishPositive
    finishBound (fun time inside => (small time inside).trans (min_le_right _ _))
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let weight := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  let historyIntegral := fun function : ℝ → ℝ =>
    ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  let center := historyIntegral (fun time => ‖quadrupoleCenter first time index - quadrupoleCenter second time index‖ /
    changed.location (index.val + 1))
  let moment := historyIntegral (fun time => ‖relativeNormalizedFirstMoment changed first second index time‖)
  let dilation := historyIntegral (fun time => |diagonalDifference first time index - diagonalDifference second time index| /
    changed.length (index.val + 1) ^ 2)
  let shape := historyIntegral (fun time =>
    |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
      |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2|)
  let correctedPhase := historyIntegral (fun time => |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
    (cascadePairedMotion prepared) index time|)
  have actual := reconstruct prepared path index nonterminal finish finishPositive.le finishBound
    (fun time inside => (small time inside).trans (min_le_left _ _)) lift
    (fun side => (liftContinuous side).1.continuousOn) polar weight
  have history : (center + moment) + (dilation + correctedPhase) ≤
      prepared.neutralWeightedSourceBudget graph coordinate tolerance index finish := by
    simpa only [CascadeMaterialPreparedPair.neutralWeightedSourceBudget, center, moment, dilation, correctedPhase,
      historyIntegral, weight, changed, first, second, abs_div,
      abs_of_nonneg (sq_nonneg (({scales with frequency := frequency} : Scales).length (index.val + 1)))] using actualNeutral
  have centerNonnegative : 0 ≤ center := intervalIntegral.integral_nonneg finishPositive.le
    (fun _ _ => mul_nonneg (Real.exp_pos _).le (div_nonneg (norm_nonneg _) (changed.location_pos _).le))
  have momentNonnegative : 0 ≤ moment := intervalIntegral.integral_nonneg finishPositive.le
    (fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  have lengthSmall := (lengths (index.val + 1)).le
  have coefficientBound : changed.length (index.val + 1) / (4 * changed.location (index.val + 1)) ≤ constant := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) (changed.location_pos (index.val + 1)))).mpr
    change changed.length (index.val + 1) ≤ 1 * changed.location (index.val + 1) at lengthSmall
    nlinarith [changed.location_pos (index.val + 1)]
  have momentTerm := mul_le_mul_of_nonneg_right coefficientBound momentNonnegative
  have centerTerm := mul_nonneg (zero_le_one.trans constantOne) centerNonnegative
  have scalar : changed.length (index.val + 1) / (4 * changed.location (index.val + 1)) * moment +
      constant * ((dilation + shape) + correctedPhase) ≤ constant * ((center + moment) + (dilation + correctedPhase) + shape) := by
    nlinarith
  exact actual.trans (scalar.trans (mul_le_mul_of_nonneg_left (add_le_add_right history shape)
    (zero_le_one.trans constantOne)))

end EulerNonuniqueness.Paper
