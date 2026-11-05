import EulerNonuniqueness.Section5.CascadeStrongNeutralOriginalHistory
import EulerNonuniqueness.Section5.CascadeStrongNeutralSplitReconstruction
import EulerNonuniqueness.Section5.CascadeMacroStateCenteredBound

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

def CascadeSourcePreparedPair.finiteCoordinateSize
    {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
    {count : ℕ}
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (graph coordinate : ℝ → ℝ) (lift : Fin 2 → ℝ → ℝ) (index : Fin count) (time : ℝ) : ℝ :=
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  |(referenceStraightenedShape first graph coordinate index time).1 -
    (referenceStraightenedShape second graph coordinate index time).1| +
  |(referenceStraightenedShape first graph coordinate index time).2 -
    (referenceStraightenedShape second graph coordinate index time).2| +
  |diagonalDifference first time index - diagonalDifference second time index| / scales.length (index.val + 1) ^ 2 +
  |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
    (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time| +
  ‖relativeNormalizedFirstMoment scales first second index time‖ +
  ‖quadrupoleCenter first time index - quadrupoleCenter second time index‖ / scales.location (index.val + 1)

theorem exists_uniform_actual_finite_coordinate_geometry_of_normalForm
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
    ∀ {cap : ℝ} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {shapeRadius monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeSourcePreparedPair cap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∃ lift : Fin 2 → ℝ → ℝ,
      (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift side time : ℂ))) ∧
      ContinuousOn (prepared.finiteCoordinateSize graph coordinate lift index) (Icc 0 finish) ∧
      prepared.finiteCoordinateSize graph coordinate lift index 0 = 0 ∧
      (∀ time : ℝ, 0 ≤ prepared.finiteCoordinateSize graph coordinate lift index time) ∧
      ∀ time ∈ Icc 0 finish,
        prepared.rawSourceCenteredState time index ≤ constant * prepared.finiteCoordinateSize graph coordinate lift index time ∧
        prepared.macroSourceState time index ≤ constant *
          (prepared.finiteCoordinateSize graph coordinate lift index time +
            ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) := by
  obtain ⟨baseRadius, basePositive, baseQuarter, baseConstant, baseOne, history⟩ :=
    exists_uniform_cascade_strong_neutral_original_history graphAnalytic coordinateSmooth graphZero coordinateZero
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
  let constant := 1 + 4 * baseConstant
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith only [baseOne]
  refine ⟨radius, radiusPositive, radiusBase.trans baseQuarter, constant, constantOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative
  filter_upwards [history scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorPositive
      factorSmall thresholdSmall referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative referencePositive,
    scales.eventually_length_lt_location ratioBound alphaPositive (show (0 : ℝ) < 1 by norm_num)]
    with frequency originalHistory referenceSmall lengthSmall
  intro cap orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound small
  let changed : Scales := {scales with frequency := frequency}
  let material := prepared.toCascadeMaterialPreparedPair
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  obtain ⟨lift, liftContinuous, polar, phaseHistory, reconstruction⟩ := originalHistory material path index nonterminal finish
    finishNonnegative finishBound (fun time inside => (small time inside).trans radiusBase)
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion material side) time index| +
        |stableShape (cascadePairedMotion material side) time index| < referenceRadius := by
    fin_cases side
    · exact (small time inside).trans_lt radiusReference
    · have actual := referenceSmall material time ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩ index
      change |unstableShape second time index| + |stableShape second time index| < referenceRadius
      linarith [abs_nonneg (diagonalDifference second time index / changed.length (index.val + 1) ^ 2 - 1)]
  have chart := (regular material path index finish finishBound
    (fun side time inside => (pairedSmall side time inside).trans_le referenceChart)).1
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 finish) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, finishBound, path.stopBound]⟩
  have dilationContinuous : ContinuousOn (fun time =>
      |diagonalDifference first time index - diagonalDifference second time index| / changed.length (index.val + 1) ^ 2)
      (Icc 0 finish) := by
    intro time inside
    exact (((material.paired_diagonal_hasDerivAt 0 index (globalInside time inside)).sub
      (material.paired_diagonal_hasDerivAt 1 index (globalInside time inside))).continuousAt.abs.div_const _).continuousWithinAt
  have momentContinuous : ContinuousOn (fun time => ‖relativeNormalizedFirstMoment changed first second index time‖)
      (Icc 0 finish) := by
    intro time inside
    exact ((((material.paired_neutral_hasDerivAt 0 index (globalInside time inside)).sub
      (material.paired_neutral_hasDerivAt 1 index (globalInside time inside))).const_smul _).continuousAt.norm).continuousWithinAt
  have positions (side : Fin 2) (patch : Fin 4) :
      Continuous (fun time => patchCentroid (cascadePairedMotion material side) time index patch) := by
    fin_cases side
    · exact prepared.trajectory.movingFamily.patchCentroid_continuous index patch
    · change Continuous (fun time => patchCentroid prepared.reference time index patch)
      rw [prepared.referenceIdentity]
      exact prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous index patch
  have phaseContinuous (side : Fin 2) : ContinuousOn
      (correctedPaperPhase (phaseCorrection 1 graph) (lift side) (cascadePairedMotion material side) index) (Icc 0 finish) := by
    apply correctedPaperPhase_continuousOn_of_centroids _ _ _ _
      (fun patch => (positions side patch).continuousOn) (liftContinuous side).1.continuousOn
      (fun time inside => (pairedSmall side time inside).le.trans referenceQuarter)
    intro time inside
    have actual := smoothInside (show unstableShape (cascadePairedMotion material side) time index ∈ Metric.ball (0 : ℝ) smoothRadius by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
      exact (le_add_of_nonneg_right (abs_nonneg _)).trans_lt ((pairedSmall side time inside).trans_le referenceSmooth))
    change ContDiffAt ℝ 2 (phaseCorrection 1 graph) (unstableShape (cascadePairedMotion material side) time index) at actual
    exact actual.continuousAt
  have translationContinuous : Continuous (fun time =>
      ‖quadrupoleCenter first time index - quadrupoleCenter second time index‖ / changed.location (index.val + 1)) := by
    have actual := ((prepared.trajectory.movingFamily.quadrupoleCenter_continuous index).sub
      (prepared.referenceWitness.trajectory.movingFamily.quadrupoleCenter_continuous index)).norm.div_const
        (changed.location (index.val + 1))
    rw [← prepared.referenceIdentity] at actual
    exact actual
  have coordinateContinuous : ContinuousOn (prepared.finiteCoordinateSize graph coordinate lift index) (Icc 0 finish) :=
    (((((chart.fst.abs.add chart.snd.abs).add dilationContinuous).add
      ((phaseContinuous 0).sub (phaseContinuous 1)).abs).add momentContinuous).add translationContinuous.continuousOn)
  have phaseInitial := phaseHistory 0 (show (0 : ℝ) ∈ Icc 0 finish from ⟨le_rfl, finishNonnegative⟩)
  simp only [intervalIntegral.integral_same] at phaseInitial
  have centroidInitial := material.nonterminal_initial_centroid index nonterminal
  change ∀ patch : Fin 4, patchCentroid first 0 index patch = patchCentroid second 0 index patch at centroidInitial
  have shapeInitial : referenceStraightenedShape first graph coordinate index 0 =
      referenceStraightenedShape second graph coordinate index 0 := by
    simp only [referenceStraightenedShape, unstableShape, stableShape, radialShape, angularShape,
      positiveHalfDiagonal, negativeHalfDiagonal, centroidInitial]
  have diagonalInitial : diagonalDifference first 0 index = diagonalDifference second 0 index := by
    simp only [diagonalDifference, positiveHalfDiagonal, negativeHalfDiagonal, centroidInitial]
  have momentInitial := material.relativeNormalizedFirstMoment_initial index nonterminal
  have centerInitial := material.nonterminal_initial_center index nonterminal
  change quadrupoleCenter first 0 index = quadrupoleCenter second 0 index at centerInitial
  have initial : prepared.finiteCoordinateSize graph coordinate lift index 0 = 0 := by
    dsimp only [CascadeSourcePreparedPair.finiteCoordinateSize]
    change |(referenceStraightenedShape first graph coordinate index 0).1 -
        (referenceStraightenedShape second graph coordinate index 0).1| +
      |(referenceStraightenedShape first graph coordinate index 0).2 -
        (referenceStraightenedShape second graph coordinate index 0).2| +
      |diagonalDifference first 0 index - diagonalDifference second 0 index| / changed.length (index.val + 1) ^ 2 +
      |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion material) index 0| +
      ‖relativeNormalizedFirstMoment changed first second index 0‖ +
      ‖quadrupoleCenter first 0 index - quadrupoleCenter second 0 index‖ / changed.location (index.val + 1) = 0
    rw [shapeInitial, diagonalInitial, phaseInitial, momentInitial, centerInitial]
    simp only [sub_self, abs_zero, zero_div, norm_zero, add_zero, zero_add]
  have nonnegative (time : ℝ) : 0 ≤ prepared.finiteCoordinateSize graph coordinate lift index time := by
    have locationPositive := changed.location_pos (index.val + 1)
    dsimp only [CascadeSourcePreparedPair.finiteCoordinateSize]
    change 0 ≤ _ + _ + _ + _ + _ + _ / changed.location (index.val + 1)
    positivity
  refine ⟨lift, liftContinuous, polar, coordinateContinuous, initial, nonnegative, ?_⟩
  intro time inside
  let size := prepared.finiteCoordinateSize graph coordinate lift index time
  let moment := ‖relativeNormalizedFirstMoment changed first second index time‖
  let translation := ‖quadrupoleCenter first time index - quadrupoleCenter second time index‖ / changed.location (index.val + 1)
  let shape := |diagonalDifference first time index - diagonalDifference second time index| / changed.length (index.val + 1) ^ 2 +
    |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
    |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2| +
    |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion material) index time|
  have identity : size = shape + moment + translation := by
    dsimp only [size, shape, moment, translation, CascadeSourcePreparedPair.finiteCoordinateSize, first, second, material, changed]
    ring
  have momentNonnegative : 0 ≤ moment := norm_nonneg _
  have translationNonnegative : 0 ≤ translation := div_nonneg (norm_nonneg _) (changed.location_pos _).le
  have shapeNonnegative : 0 ≤ shape := by dsimp only [shape]; positivity
  have lengthBound : changed.length (index.val + 1) / changed.location (index.val + 1) ≤ 1 := by
    apply (div_le_one (changed.location_pos _)).mpr
    simpa only [one_mul] using (lengthSmall (index.val + 1)).le
  have momentFactor : changed.length (index.val + 1) / (4 * changed.location (index.val + 1)) ≤ 1 := by
    apply (div_le_one (mul_pos (by norm_num) (changed.location_pos _))).mpr
    have actual := (div_le_one (changed.location_pos _)).mp lengthBound
    linarith [changed.location_pos (index.val + 1)]
  have reconstructed := reconstruction time inside
  change _ ≤ (changed.length (index.val + 1) / (4 * changed.location (index.val + 1))) * moment +
    baseConstant * shape at reconstructed
  have centerIdentity : prepared.rawSourceCenteredState time index =
      ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / changed.length (index.val + 1) := by
    dsimp only [CascadeSourcePreparedPair.rawSourceCenteredState, first, second, changed]
    rw [prepared.referenceIdentity, norm_sub_rev]
  rw [← centerIdentity] at reconstructed
  have centerBound : prepared.rawSourceCenteredState time index ≤ baseConstant * size := by
    have multiplied := mul_le_mul_of_nonneg_right momentFactor momentNonnegative
    have translate := mul_nonneg (show 0 ≤ baseConstant by linarith only [baseOne]) translationNonnegative
    rw [identity]
    calc
      prepared.rawSourceCenteredState time index ≤
          (changed.length (index.val + 1) / (4 * changed.location (index.val + 1))) * moment + baseConstant * shape := reconstructed
      _ ≤ moment + baseConstant * shape := by simpa only [one_mul] using add_le_add_right multiplied (baseConstant * shape)
      _ ≤ baseConstant * moment + baseConstant * shape :=
        add_le_add_right (by simpa only [one_mul] using mul_le_mul_of_nonneg_right baseOne momentNonnegative) _
      _ ≤ baseConstant * moment + baseConstant * shape + baseConstant * translation := le_add_of_nonneg_right translate
      _ = baseConstant * (shape + moment + translation) := by ring
  have sizeNonnegative : 0 ≤ size := nonnegative time
  have finalCenter : prepared.rawSourceCenteredState time index ≤ constant * size := by
    apply centerBound.trans
    exact mul_le_mul_of_nonneg_right (by dsimp only [constant]; linarith only [baseOne]) sizeNonnegative
  have macroBound := prepared.macroSourceState_le_centered_and_raw path
    (show time ∈ Icc 0 path.stop from ⟨inside.1, inside.2.trans finishBound⟩) index
  rw [norm_sub_rev, ← prepared.referenceIdentity] at macroBound
  change prepared.macroSourceState time index ≤ translation +
    4 * (changed.length (index.val + 1) / changed.location (index.val + 1)) * prepared.rawSourceCenteredState time index + _ at macroBound
  have centerNonnegative : 0 ≤ prepared.rawSourceCenteredState time index := by
    dsimp only [CascadeSourcePreparedPair.rawSourceCenteredState]
    exact div_nonneg (norm_nonneg _) (changed.length_pos _).le
  have rawNonnegative : 0 ≤ ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch := by
    apply Finset.sum_nonneg
    intro patch _
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have translationBound : translation ≤ size := by rw [identity]; linarith only [shapeNonnegative, momentNonnegative]
  have factorBound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left lengthBound (by norm_num : (0 : ℝ) ≤ 4)) centerNonnegative
  refine ⟨finalCenter, ?_⟩
  calc
    prepared.macroSourceState time index ≤ translation +
        4 * (changed.length (index.val + 1) / changed.location (index.val + 1)) * prepared.rawSourceCenteredState time index +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch := macroBound
    _ ≤ size + 4 * prepared.rawSourceCenteredState time index +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch := by
      apply add_le_add_right
      exact add_le_add translationBound (by simpa only [mul_one] using factorBound)
    _ ≤ size + 4 * (baseConstant * size) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch :=
      add_le_add_right (add_le_add_left (mul_le_mul_of_nonneg_left centerBound (by norm_num)) _) _
    _ = constant * size + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch := by dsimp only [constant]; ring
    _ ≤ constant * size + constant * ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch :=
      add_le_add_left (by simpa only [one_mul] using mul_le_mul_of_nonneg_right constantOne rawNonnegative) _
    _ = constant * (size + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) := by ring

end EulerNonuniqueness.Paper
