import EulerNonuniqueness.Section5.CascadeFiniteCoordinateGeometry
import EulerNonuniqueness.Section6.NormalFormChartComparison

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_actual_finite_coordinate_chart_comparison
    {baseGraph baseCoordinate outputGraph outputCoordinate : ℝ → ℝ}
    (baseGraphAnalytic : AnalyticAt ℝ baseGraph 0)
    (baseCoordinateSmooth : ContDiffAt ℝ 2 baseCoordinate 0)
    (baseGraphZero : baseGraph 0 = 0) (baseCoordinateZero : baseCoordinate 0 = 0)
    (baseGraphDerivative : HasDerivAt baseGraph 0 0)
    (baseCoordinateDerivative : HasDerivAt baseCoordinate 1 0)
    (outputGraphAnalytic : AnalyticAt ℝ outputGraph 0)
    (outputCoordinateSmooth : ContDiffAt ℝ 2 outputCoordinate 0)
    (outputGraphZero : outputGraph 0 = 0) (outputCoordinateZero : outputCoordinate 0 = 0)
    (outputGraphDerivative : HasDerivAt outputGraph 0 0)
    (outputCoordinateDerivative : HasDerivAt outputCoordinate 1 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
    ∀ {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
      {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ lift : Fin 2 → ℝ → ℝ, ∀ index : Fin count, ∀ time : ℝ,
    |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| < radius →
    |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < radius →
    prepared.finiteCoordinateSize outputGraph outputCoordinate lift index time ≤
        constant * prepared.finiteCoordinateSize baseGraph baseCoordinate lift index time ∧
      prepared.finiteCoordinateSize outputGraph outputCoordinate lift index time +
          (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) ≤
        constant * (prepared.finiteCoordinateSize baseGraph baseCoordinate lift index time +
          ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) := by
  obtain ⟨chartRadius, chartPositive, constant, constantOne, chartComparison⟩ :=
    localNormalFormChart_exists_uniform_comparison baseGraphAnalytic baseCoordinateSmooth
      baseGraphZero baseCoordinateZero baseGraphDerivative baseCoordinateDerivative
      outputGraphAnalytic outputCoordinateSmooth outputGraphZero outputCoordinateZero
      outputGraphDerivative outputCoordinateDerivative
  refine ⟨min chartRadius (1 / 4), lt_min chartPositive (by norm_num), min_le_right _ _,
    constant, constantOne, ?_⟩
  intro cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor
    boundaryConstant count prepared lift index time alternativeSmall referenceSmall
  let alternative := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.reference
  let firstPoint := (unstableShape alternative time index, stableShape alternative time index)
  let secondPoint := (unstableShape reference time index, stableShape reference time index)
  let baseShape :=
    |(referenceStraightenedShape alternative baseGraph baseCoordinate index time).1 -
        (referenceStraightenedShape reference baseGraph baseCoordinate index time).1| +
      |(referenceStraightenedShape alternative baseGraph baseCoordinate index time).2 -
        (referenceStraightenedShape reference baseGraph baseCoordinate index time).2|
  let outputShape :=
    |(referenceStraightenedShape alternative outputGraph outputCoordinate index time).1 -
        (referenceStraightenedShape reference outputGraph outputCoordinate index time).1| +
      |(referenceStraightenedShape alternative outputGraph outputCoordinate index time).2 -
        (referenceStraightenedShape reference outputGraph outputCoordinate index time).2|
  let phaseChange :=
    (phaseCorrection 1 outputGraph firstPoint.1 - phaseCorrection 1 baseGraph firstPoint.1) -
      (phaseCorrection 1 outputGraph secondPoint.1 - phaseCorrection 1 baseGraph secondPoint.1)
  let basePhase := relativeCorrectedPaperPhase (phaseCorrection 1 baseGraph) lift
    (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time
  let outputPhase := relativeCorrectedPaperPhase (phaseCorrection 1 outputGraph) lift
    (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time
  have shapeComparison : outputShape + |phaseChange| ≤ constant * baseShape := by
    simpa only [outputShape, baseShape, phaseChange, referenceStraightenedShape, firstPoint, secondPoint]
      using chartComparison firstPoint secondPoint
        (alternativeSmall.trans_le (min_le_left _ _)) (referenceSmall.trans_le (min_le_left _ _))
  have pairedAlternative : cascadePairedMotion prepared.toCascadeMaterialPreparedPair 0 = alternative := rfl
  have pairedReference : cascadePairedMotion prepared.toCascadeMaterialPreparedPair 1 = reference := rfl
  have phaseIdentity : outputPhase = basePhase - phaseChange := by
    dsimp only [outputPhase, basePhase, phaseChange, relativeCorrectedPaperPhase, correctedPaperPhase,
      firstPoint, secondPoint]
    simp only [pairedAlternative, pairedReference]
    ring
  have phaseComparison : |outputPhase| ≤ |basePhase| + |phaseChange| := by
    rw [phaseIdentity]
    exact abs_sub _ _
  let dilation := |diagonalDifference alternative time index - diagonalDifference reference time index| /
    scales.length (index.val + 1) ^ 2
  let moment := ‖relativeNormalizedFirstMoment scales alternative reference index time‖
  let translation := ‖quadrupoleCenter alternative time index - quadrupoleCenter reference time index‖ /
    scales.location (index.val + 1)
  have dilationNonnegative : 0 ≤ dilation := div_nonneg (abs_nonneg _) (sq_nonneg _)
  have momentNonnegative : 0 ≤ moment := norm_nonneg _
  have translationNonnegative : 0 ≤ translation :=
    div_nonneg (norm_nonneg _) (scales.location_pos _).le
  have remainderNonnegative : 0 ≤ |basePhase| + dilation + moment + translation := by positivity
  have remainderScaled := mul_nonneg (sub_nonneg.mpr constantOne) remainderNonnegative
  have coordinateComparison : prepared.finiteCoordinateSize outputGraph outputCoordinate lift index time ≤
      constant * prepared.finiteCoordinateSize baseGraph baseCoordinate lift index time := by
    change outputShape + dilation + |outputPhase| + moment + translation ≤
      constant * (baseShape + dilation + |basePhase| + moment + translation)
    nlinarith only [shapeComparison, phaseComparison, remainderScaled]
  refine ⟨coordinateComparison, ?_⟩
  have rawNonnegative : 0 ≤ ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch := by
    apply Finset.sum_nonneg
    intro patch _
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have rawScaled := mul_nonneg (sub_nonneg.mpr constantOne) rawNonnegative
  nlinarith only [coordinateComparison, rawScaled]

end EulerNonuniqueness.Paper
