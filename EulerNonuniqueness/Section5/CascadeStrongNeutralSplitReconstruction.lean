import EulerNonuniqueness.Section5.CascadeStrongNeutralWeightedReconstruction
import EulerNonuniqueness.Section5.CascadePairedChartRegularity
import EulerNonuniqueness.General.WeightedTriangularFeedback

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_strong_neutral_split_reconstruction
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {scaleRoot boundaryConstant factor threshold referenceConstant : ℝ},
    0 < scaleRoot → 0 ≤ boundaryConstant → factor ≤ 1 / 8 →
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
    ∀ lift : Fin 2 → ℝ → ℝ, (∀ side, ContinuousOn (lift side) (Icc 0 finish)) →
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared side) time index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared side) time index‖ : ℂ) *
          Complex.exp (Complex.I * (lift side time : ℂ))) →
    ∀ weight : ℝ,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let historyIntegral := fun function : ℝ → ℝ =>
      ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
    historyIntegral (fun time =>
      ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
          changed.length (index.val + 1)) ≤
      (changed.length (index.val + 1) / (4 * changed.location (index.val + 1))) *
        historyIntegral (fun time => ‖relativeNormalizedFirstMoment changed first second index time‖) +
      constant * ((historyIntegral (fun time =>
        |diagonalDifference first time index - diagonalDifference second time index| / changed.length (index.val + 1) ^ 2) +
        historyIntegral (fun time =>
          |(referenceStraightenedShape first graph coordinate index time).1 -
            (referenceStraightenedShape second graph coordinate index time).1| +
          |(referenceStraightenedShape first graph coordinate index time).2 -
            (referenceStraightenedShape second graph coordinate index time).2|)) +
        historyIntegral (fun time => |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
          (cascadePairedMotion prepared) index time|)) := by
  obtain ⟨baseRadius, basePositive, baseQuarter, constant, constantOne, bound⟩ :=
    exists_uniform_cascade_strong_neutral_weighted_reconstruction graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨chartRadius, chartPositive, _, regular⟩ :=
    exists_uniform_cascade_paired_chart_regularity graphAnalytic.contDiffAt coordinateSmooth
  obtain ⟨correctionSmooth, _, _, _, _, _, _, _⟩ :=
    sameGraph_phaseCorrection_exists_uniform_stable_factor graphAnalytic graphZero graphDerivative coordinateZero coordinateDerivative
  obtain ⟨smoothRadius, smoothPositive, smoothInside⟩ := Metric.mem_nhds_iff.mp
    (correctionSmooth.eventually (by norm_num))
  let referenceRadius := min chartRadius (min smoothRadius (1 / 4))
  let radius := min baseRadius (referenceRadius / 2)
  have referencePositive : 0 < referenceRadius := by dsimp only [referenceRadius]; positivity
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusBase : radius ≤ baseRadius := min_le_left _ _
  have radiusReference : radius < referenceRadius := (min_le_right _ _).trans_lt (by linarith)
  have referenceChart : referenceRadius ≤ chartRadius := min_le_left _ _
  have referenceQuarter : referenceRadius ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have referenceSmooth : referenceRadius ≤ smoothRadius := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨radius, radiusPositive, radiusBase.trans baseQuarter, constant, constantOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorSmall thresholdSmall referenceNonnegative
  filter_upwards [bound scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorSmall
      thresholdSmall referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative referencePositive]
    with frequency reconstruction referenceSmall
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound small lift liftContinuous polar weight
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| < referenceRadius := by
    fin_cases side
    · exact (small time inside).trans_lt radiusReference
    · have actual := referenceSmall prepared time ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩ index
      change |unstableShape second time index| + |stableShape second time index| < referenceRadius
      linarith [abs_nonneg (diagonalDifference second time index / changed.length (index.val + 1) ^ 2 - 1)]
  have chart := (regular prepared path index finish finishBound
    (fun side time inside => (pairedSmall side time inside).trans_le referenceChart)).1
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 finish) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, finishBound, path.stopBound]⟩
  have dilationContinuous : ContinuousOn (fun time =>
      |diagonalDifference first time index - diagonalDifference second time index| / changed.length (index.val + 1) ^ 2)
      (Icc 0 finish) := by
    intro time inside
    exact (((prepared.paired_diagonal_hasDerivAt 0 index (globalInside time inside)).sub
      (prepared.paired_diagonal_hasDerivAt 1 index (globalInside time inside))).continuousAt.abs.div_const _).continuousWithinAt
  have momentContinuous : ContinuousOn (fun time => ‖relativeNormalizedFirstMoment changed first second index time‖)
      (Icc 0 finish) := by
    intro time inside
    exact ((((prepared.paired_neutral_hasDerivAt 0 index (globalInside time inside)).sub
      (prepared.paired_neutral_hasDerivAt 1 index (globalInside time inside))).const_smul _).continuousAt.norm).continuousWithinAt
  have positions (side : Fin 2) (patch : Fin 4) :
      Continuous (fun time => patchCentroid (cascadePairedMotion prepared side) time index patch) := by
    fin_cases side
    · exact prepared.trajectory.movingFamily.patchCentroid_continuous index patch
    · simpa only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] using
        prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous index patch
  have phaseContinuous (side : Fin 2) : ContinuousOn
      (correctedPaperPhase (phaseCorrection 1 graph) (lift side) (cascadePairedMotion prepared side) index) (Icc 0 finish) := by
    apply correctedPaperPhase_continuousOn_of_centroids _ _ _ _
      (fun patch => (positions side patch).continuousOn) (liftContinuous side)
      (fun time inside => (pairedSmall side time inside).le.trans referenceQuarter)
    intro time inside
    have actual := smoothInside (show unstableShape (cascadePairedMotion prepared side) time index ∈ Metric.ball (0 : ℝ) smoothRadius by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
      exact (le_add_of_nonneg_right (abs_nonneg _)).trans_lt ((pairedSmall side time inside).trans_le referenceSmooth))
    change ContDiffAt ℝ 2 (phaseCorrection 1 graph) (unstableShape (cascadePairedMotion prepared side) time index) at actual
    exact actual.continuousAt
  have phaseDifferenceContinuous : ContinuousOn (fun time =>
      |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared) index time|) (Icc 0 finish) :=
    ((phaseContinuous 0).sub (phaseContinuous 1)).abs
  have shapeContinuous : ContinuousOn (fun time =>
      |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
        |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2|)
      (Icc 0 finish) := chart.fst.abs.add chart.snd.abs
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have momentIntegrable := (weightContinuous.continuousOn.mul momentContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have dilationIntegrable := (weightContinuous.continuousOn.mul dilationContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have shapeIntegrable := (weightContinuous.continuousOn.mul shapeContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have unstableIntegrable := (weightContinuous.continuousOn.mul chart.fst.abs).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have stableIntegrable := (weightContinuous.continuousOn.mul chart.snd.abs).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  simp only [Prod.fst_sub] at unstableIntegrable
  simp only [Prod.snd_sub] at stableIntegrable
  have phaseIntegrable := (weightContinuous.continuousOn.mul phaseDifferenceContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have actual := reconstruction prepared path index nonterminal finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans radiusBase) lift liftContinuous polar weight
  apply actual.trans_eq
  simp_rw [mul_add, mul_left_comm _ constant,
    mul_left_comm _ (({scales with frequency := frequency} : Scales).length (index.val + 1) /
      (4 * ({scales with frequency := frequency} : Scales).location (index.val + 1)))]
  rw [intervalIntegral.integral_add (momentIntegrable.const_mul _)
    ((((dilationIntegrable.const_mul _).add (unstableIntegrable.const_mul _)).add
      (stableIntegrable.const_mul _)).add (phaseIntegrable.const_mul _)),
    intervalIntegral.integral_add (((dilationIntegrable.const_mul _).add
      (unstableIntegrable.const_mul _)).add (stableIntegrable.const_mul _)) (phaseIntegrable.const_mul _),
    intervalIntegral.integral_add ((dilationIntegrable.const_mul _).add (unstableIntegrable.const_mul _))
      (stableIntegrable.const_mul _),
    intervalIntegral.integral_add (dilationIntegrable.const_mul _) (unstableIntegrable.const_mul _)]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add unstableIntegrable stableIntegrable]
  ring

end EulerNonuniqueness.Paper
