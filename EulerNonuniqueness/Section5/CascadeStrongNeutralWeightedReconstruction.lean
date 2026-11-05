import EulerNonuniqueness.Section5.CascadeStrongNeutralReconstruction
import EulerNonuniqueness.Section5.CascadeClosedSaddleDynamics
import EulerNonuniqueness.Section5.CascadeCorrectedPhaseDynamics
import EulerNonuniqueness.Section5.CascadeRelativeDilationHistory
import EulerNonuniqueness.Section6.PaperCorrectedPhaseContinuity
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity
import EulerNonuniqueness.General.NonnegativeIntervalMajorant

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_strong_neutral_weighted_reconstruction
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
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / changed.length (index.val + 1))) ≤
      ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        ((changed.length (index.val + 1) / (4 * changed.location (index.val + 1))) *
            ‖relativeNormalizedFirstMoment changed first second index time‖ +
          constant * (|diagonalDifference first time index - diagonalDifference second time index| / changed.length (index.val + 1) ^ 2 +
            |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
            |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2| +
            |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared) index time|)) := by
  obtain ⟨correctionSmooth, _, _, _, _, _, _, _⟩ :=
    sameGraph_phaseCorrection_exists_uniform_stable_factor graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  obtain ⟨pointRadius, pointPositive, pointQuarter, constant, constantOne, reconstruction⟩ :=
    exists_uniform_cascade_strong_neutral_reconstruction graphAnalytic.contDiffAt coordinateSmooth
      (correctionSmooth.of_le (by norm_num)) graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨chartRadius, chartPositive, _, closedChart⟩ :=
    exists_uniform_cascade_closed_saddle_dynamics graphAnalytic.contDiffAt coordinateSmooth
  obtain ⟨smoothRadius, smoothPositive, smoothInside⟩ := Metric.mem_nhds_iff.mp
    (correctionSmooth.eventually (by norm_num))
  let referenceRadius := min chartRadius (min (smoothRadius / 2) (1 / 4))
  let radius := min pointRadius (referenceRadius / 2)
  have referencePositive : 0 < referenceRadius := by dsimp only [referenceRadius]; positivity
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusPoint : radius ≤ pointRadius := min_le_left _ _
  have radiusReference : radius < referenceRadius := (min_le_right _ _).trans_lt (by linarith)
  have referenceChart : referenceRadius ≤ chartRadius := min_le_left _ _
  have referenceQuarter : referenceRadius ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have referenceSmooth : referenceRadius < smoothRadius :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  refine ⟨radius, radiusPositive, radiusPoint.trans pointQuarter, constant, constantOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorSmall thresholdSmall referenceNonnegative
  filter_upwards [reconstruction scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      thresholdSmall referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative referencePositive]
    with frequency pointBound referenceSmall
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
    · have sharp := referenceSmall prepared time
        (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩) index
      change |unstableShape second time index| + |stableShape second time index| < referenceRadius
      linarith [abs_nonneg (diagonalDifference second time index / changed.length (index.val + 1) ^ 2 - 1)]
  have radial : ∀ time ∈ Icc 0 finish, |radialShape first time index| ≤ 1 / 2 := by
    intro time inside
    rw [radialShape_eq_unstable_add_stable]
    exact (abs_add _ _).trans ((small time inside).trans ((radiusPoint.trans pointQuarter).trans (by norm_num)))
  have positions (side : Fin 2) (patch : Fin 4) :
      Continuous (fun time => patchCentroid (cascadePairedMotion prepared side) time index patch) := by
    fin_cases side
    · exact prepared.trajectory.movingFamily.patchCentroid_continuous index patch
    · simpa only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] using
        prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous index patch
  have phaseContinuous (side : Fin 2) : ContinuousOn
      (correctedPaperPhase (phaseCorrection 1 graph) (lift side) (cascadePairedMotion prepared side) index) (Icc 0 finish) := by
    apply correctedPaperPhase_continuousOn_of_centroids _ _ _ _ (fun patch => (positions side patch).continuousOn)
      (liftContinuous side) (fun time inside => (pairedSmall side time inside).le.trans referenceQuarter)
    intro time inside
    have smooth := smoothInside (show unstableShape (cascadePairedMotion prepared side) time index ∈ Metric.ball (0 : ℝ) smoothRadius by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
      exact (le_add_of_nonneg_right (abs_nonneg _)).trans_lt
        ((pairedSmall side time inside).trans referenceSmooth))
    change ContDiffAt ℝ 2 (phaseCorrection 1 graph) (unstableShape (cascadePairedMotion prepared side) time index) at smooth
    exact smooth.continuousAt
  have phaseDifferenceContinuous : ContinuousOn
      (relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared) index) (Icc 0 finish) :=
    (phaseContinuous 0).sub (phaseContinuous 1)
  have chartContinuous : ContinuousOn (fun time => referenceStraightenedShape first graph coordinate index time -
      referenceStraightenedShape second graph coordinate index time) (Icc 0 finish) := by
    intro time inside
    exact (closedChart prepared path index time ⟨inside.1, inside.2.trans finishBound⟩
      (fun side => (pairedSmall side time inside).trans_le referenceChart)).continuousAt.continuousWithinAt
  have dilationContinuous : ContinuousOn (fun time =>
      (diagonalDifference first time index - diagonalDifference second time index) / changed.length (index.val + 1) ^ 2) (Icc 0 finish) := by
    intro time inside
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith [inside.1], by linarith [inside.2, finishBound, path.stopBound]⟩
    exact (((prepared.paired_diagonal_hasDerivAt 0 index globalInside).sub
      (prepared.paired_diagonal_hasDerivAt 1 index globalInside)).div_const _).continuousAt.continuousWithinAt
  have momentContinuous : ContinuousOn (relativeNormalizedFirstMoment changed first second index) (Icc 0 finish) := by
    intro time inside
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith [inside.1], by linarith [inside.2, finishBound, path.stopBound]⟩
    exact (((prepared.paired_neutral_hasDerivAt 0 index globalInside).sub
      (prepared.paired_neutral_hasDerivAt 1 index globalInside)).const_smul _).continuousAt.continuousWithinAt
  have normalizedDilation : ContinuousOn (fun time =>
      |diagonalDifference first time index - diagonalDifference second time index| / changed.length (index.val + 1) ^ 2) (Icc 0 finish) := by
    simpa only [abs_div, abs_of_pos (sq_pos_of_pos (changed.length_pos _))] using dilationContinuous.abs
  have majorantContinuous : ContinuousOn (fun time => Real.exp (-weight * time) *
      ((changed.length (index.val + 1) / (4 * changed.location (index.val + 1))) *
          ‖relativeNormalizedFirstMoment changed first second index time‖ +
        constant * (|diagonalDifference first time index - diagonalDifference second time index| / changed.length (index.val + 1) ^ 2 +
          |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
          |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2| +
          |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared) index time|))) (Icc 0 finish) := by
    have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
    exact weightContinuous.continuousOn.mul ((continuousOn_const.mul momentContinuous.norm).add
      (continuousOn_const.mul (((normalizedDilation.add chartContinuous.fst.abs).add chartContinuous.snd.abs).add phaseDifferenceContinuous.abs)))
  apply EulerNonuniqueness.General.intervalIntegral_le_of_nonnegative_majorant finishNonnegative
    (fun _ _ => mul_nonneg (Real.exp_pos _).le (div_nonneg (norm_nonneg _) (changed.length_pos _).le)) majorantContinuous
  intro time inside
  exact mul_le_mul_of_nonneg_left
    (pointBound prepared path factorSmall index nonterminal finish finishNonnegative finishBound radial time inside
      ((small time inside).trans radiusPoint) (lift 0) (lift 1) (polar 0 time inside) (polar 1 time inside)) (Real.exp_pos _).le

end EulerNonuniqueness.Paper
