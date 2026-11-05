import EulerNonuniqueness.Section5.CascadeTerminalMatchedFirstHit
import EulerNonuniqueness.Section5.CascadeSourceStoppedSmallFactors
import EulerNonuniqueness.Section6.SourcePacketTerminalSectionSelection
import EulerNonuniqueness.Section1.CascadeSourceRateRatioChoice

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

/-- Actual finite terminal matches exist with parameters fixed across every count and arbitrarily large frequencies. -/
theorem exists_actual_terminal_matched_first_hit_family
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    {alpha : ℝ} (alphaPositive : 0 < alpha) (alphaSmall : alpha < 1) :
    ∃ sectionTime > (0 : ℝ), ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ rawCap > (0 : ℝ), ∃ shapeRadius > (0 : ℝ), ∃ factor > (0 : ℝ), factor ≤ 1 / 100 ∧
      ∃ monitor > (0 : ℝ), ∃ boundaryConstant ≥ (1 : ℝ),
      ∃ endpoint > (0 : ℝ), endpoint ≤ 1 ∧ ∃ incomingTime : ℝ,
      incomingTime < sectionTime ∧ 0 < coordinate (orbitUnstableShape orbit incomingTime) ∧
      coordinate (orbitUnstableShape orbit incomingTime) ≤ endpoint / 2 ∧
      ∀ matchingAccuracy : ℝ, 0 < matchingAccuracy → ∀ precision : ℝ, 0 < precision →
      ∃ ratio > (2 : ℝ), ∃ threshold > (0 : ℝ), threshold < 1 / 8 ∧
      ∃ scaleRoot ≥ (8 : ℝ), ∃ referenceConstant > (0 : ℝ), referenceConstant ≤ scaleRoot ^ 3 ∧
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, 2 ≤ count →
      ∃ phase dipoleAngle : ℕ → ℝ,
      PrescribedCascadePhases ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩ orbit sectionTime count phase dipoleAngle ∧
      ∃ prepared : CascadeSourcePreparedPair rawCap ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩ orbit sectionTime
        phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∃ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∃ index source : Fin count, index.val + 1 = source.val ∧ source.val + 1 = count ∧
      let changed : Scales := ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩
      let motion := prepared.trajectory.movingFamily.patchMotion
      let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
      let finish := Real.log (endpoint / changed.seed (index.val + 1)) / growth
      0 < finish ∧ finish < 1 / 4 ∧ finish ≤ path.stop ∧
      changed.seed (index.val + 1) * Real.exp (growth * finish) = endpoint ∧
      (∃ hit : ℝ, 0 < hit ∧ hit ≤ finish ∧
        (referenceStraightenedShape motion graph coordinate index hit -
          referenceStraightenedShape prepared.reference graph coordinate index hit).1 =
          coordinate (orbitUnstableShape orbit incomingTime) ∧
        (∀ time : ℝ, 0 ≤ time → time < hit →
          (referenceStraightenedShape motion graph coordinate index time -
            referenceStraightenedShape prepared.reference graph coordinate index time).1 <
            coordinate (orbitUnstableShape orbit incomingTime)) ∧
        ∃ rotation : ℂ,
          halfDiagonalMatchingRotation (positiveHalfDiagonal motion hit index) (orbit.positive incomingTime) = rotation ∧
          ‖rotation‖ = 1 ∧
          ‖cascadeNormalizedPointPositions changed motion index hit rotation 0 -
            centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ < matchingAccuracy) ∧
      ∃ lift : Fin count → Fin 2 → ℝ → ℝ,
        ∀ time ∈ Icc 0 finish, ∀ receiver : Fin count, receiver.val < index.val →
          prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
            ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch ≤ precision := by
  classical
  obtain ⟨sectionTime, sectionPositive, initialError, errorPositive, errorSmall, radiusLarge,
    separationClose, outgoing, numericBudget⟩ :=
    normalizedSeparatingOrbit_terminal_signed_section orbit normalized (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    compatible, rawCap, capPositive, factors⟩ :=
    exists_uniform_actual_terminal_matched_first_hit orbit normalized sectionTime initialError sectionPositive
      errorPositive.le errorSmall radiusLarge separationClose outgoing numericBudget
  obtain ⟨shapeRadius, shapePositive, factorMax, factorMaxPositive, factorMaxSmall, preparations⟩ :=
    exists_uniform_source_stopped_cascade_parameters_for_small_factors orbit normalized sectionPositive
  let factor := factorMax / 2
  have factorPositive : 0 < factor := half_pos factorMaxPositive
  have factorBound : factor ≤ factorMax := (half_lt_self factorMaxPositive).le
  have factorSmall : factor ≤ 1 / 100 := factorBound.trans factorMaxSmall
  obtain ⟨monitor, monitorPositive, boundaryConstant, boundaryOne, parameters⟩ :=
    preparations factor factorPositive factorBound rawCap capPositive
  obtain ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRadius, targetRadiusPositive,
    targetRadiusQuarter, matchedRoot, matchedRootEight, radius, radiusPositive, radiusQuarter,
    endpointMax, endpointMaxPositive, endpointMaxOne, incoming⟩ := factors factorPositive factorSmall
  let endpoint := endpointMax / 2
  have endpointPositive : 0 < endpoint := half_pos endpointMaxPositive
  have endpointBound : endpoint ≤ endpointMax := (half_lt_self endpointMaxPositive).le
  have endpointOne : endpoint ≤ 1 := endpointBound.trans endpointMaxOne
  obtain ⟨incomingTime, incomingBefore, targetPositive, targetBound, matching⟩ :=
    (incoming endpoint endpointPositive endpointBound).exists
  refine ⟨sectionTime, sectionPositive, graph, coordinate, graphAnalytic, graphZero, graphDerivative,
    coordinateSmooth, coordinateZero, coordinateDerivative, rawCap, capPositive, shapeRadius, shapePositive,
    factor, factorPositive, factorSmall, monitor, monitorPositive, boundaryConstant, boundaryOne,
    endpoint, endpointPositive, endpointOne, incomingTime, incomingBefore, targetPositive, targetBound, ?_⟩
  intro matchingAccuracy matchingPositive precision precisionPositive
  obtain ⟨matchedRatio, matchedRatioTwo, matchedScales⟩ := matching matchingAccuracy matchingPositive precision precisionPositive
  obtain ⟨ratio, ratioLower, ratioChoices⟩ := exists_cascade_source_rate_ratio_threshold
    alphaPositive alphaSmall (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1 / 8)
    (max 3 matchedRatio) ((2 * Real.sqrt 2 + 1) * 8)
  have ratioThree : 3 ≤ ratio := (le_max_left _ _).trans ((le_max_right _ _).trans ratioLower)
  have ratioLarge : 2 < ratio := by linarith only [ratioThree]
  have matchedRatioBound : matchedRatio ≤ ratio := (le_max_right _ _).trans ((le_max_right _ _).trans ratioLower)
  obtain ⟨ratioPower, ratioSeparation, _⟩ := ratioChoices ratio le_rfl
  obtain ⟨threshold, thresholdPositive, thresholdBound, thresholdSmall, constructorRoot,
    constructorRootEight, constructions⟩ := parameters alphaPositive alphaSmall ratioLarge thresholdMax thresholdPositive
      (tolerance := 1 / 16) (timingConstant := 1) (by norm_num) (by norm_num) (by norm_num)
  let scaleRoot := max matchedRoot constructorRoot
  have matchedRootBound : matchedRoot ≤ scaleRoot := le_max_left _ _
  have constructorRootBound : constructorRoot ≤ scaleRoot := le_max_right _ _
  have rootEight : 8 ≤ scaleRoot := matchedRootEight.trans matchedRootBound
  obtain ⟨referenceConstant, referencePositive, referenceAmplitude, actual⟩ := constructions scaleRoot constructorRootBound
  let base : Scales := ⟨alpha, scaleRoot ^ 3, ratio, 0⟩
  have matched := matchedScales base scaleRoot matchedRootBound rfl matchedRatioBound alphaPositive alphaSmall ratioPower
    referenceConstant referencePositive.le referenceAmplitude threshold thresholdBound.le boundaryConstant boundaryOne ratioSeparation
  refine ⟨ratio, ratioLarge, threshold, thresholdPositive, thresholdSmall, scaleRoot, rootEight,
    referenceConstant, referencePositive, referenceAmplitude, ?_⟩
  filter_upwards [actual, matched] with frequency actualAt matchedAt
  intro count countLarge
  obtain ⟨phase, dipoleAngle, prescribed, prepared, pathExists⟩ := actualAt.2 count countLarge
  obtain ⟨path⟩ := pathExists
  let index : Fin count := ⟨count - 2, by omega⟩
  let source : Fin count := ⟨count - 1, by omega⟩
  have adjacent : index.val + 1 = source.val := by dsimp only [index, source]; omega
  have terminal : source.val + 1 = count := by dsimp only [source]; omega
  have data := matchedAt count phase dipoleAngle prepared path index source adjacent terminal prescribed
  dsimp only at data
  obtain ⟨finishPositive, finishQuarter, _, exposure, available, _, hitData, _, _,
    coarseLift, _, _, coarseFull⟩ := data
  refine ⟨phase, dipoleAngle, prescribed, prepared, path, index, source, adjacent, terminal, ?_⟩
  dsimp only
  exact ⟨finishPositive, finishQuarter, available, exposure, hitData, coarseLift, coarseFull⟩

end EulerNonuniqueness.Paper
