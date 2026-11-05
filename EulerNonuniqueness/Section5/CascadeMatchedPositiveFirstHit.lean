import EulerNonuniqueness.Section5.CascadePositiveFirstHit
import EulerNonuniqueness.Section5.CascadeAccurateStraightenedHitMatch
import EulerNonuniqueness.Section5.CascadeFullStatePhysicalRefinement

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_matched_positive_first_hit
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (sectionTime : ℝ) (sectionPositive : 0 < sectionTime) :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ),
      ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ currentMagnitude ≥ (1 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      ∃ rootMin ≥ (8 : ℝ), ∃ endpointMax > (0 : ℝ),
      endpointMax ≤ 1 ∧ ∀ endpoint : ℝ, 0 < endpoint → endpoint ≤ endpointMax →
      ∀ᶠ incomingTime : ℝ in atBot,
      incomingTime < sectionTime ∧ 0 < coordinate (orbitUnstableShape orbit incomingTime) ∧
      coordinate (orbitUnstableShape orbit incomingTime) ≤ endpoint / 2 ∧
      ∀ matchingAccuracy : ℝ, 0 < matchingAccuracy → ∀ precision : ℝ, 0 < precision →
      ∀ extent magnitudeMax distanceMax sourceRate : ℝ,
      1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < sourceRate → sourceRate < 1 / 8 →
      ∀ initialError : ℝ, initialError ≤ 1 / 64 → ∀ phaseTolerance : ℝ, 0 ≤ phaseTolerance →
      ∃ ratioMin ≥ (2 : ℝ),
      ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
      ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
      ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
      ∀ boundaryConstant timingError : ℝ,
      1 ≤ boundaryConstant → 0 ≤ timingError →
      3 * timingError + 2 * phaseTolerance ≤ 1 / 2 →
      (sourceRate * scales.ratio + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      PrescribedCascadePhases {scales with frequency := frequency} orbit sectionTime count phase dipoleAngle →
      ∀ (index : Fin count) (nonterminal : index.val + 1 < count), index.val + 2 < count →
      ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
      let changed : Scales := {scales with frequency := frequency}
      let motion := prepared.trajectory.movingFamily.patchMotion
      (∀ source : Fin count, index.val < source.val →
        let length := changed.length (source.val + 1)
        0 ≤ entry source ∧ entry source ≤ path.stop ∧ 512 ≤ initialDistance source ∧
        initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
        ‖firstDipoleSeparation motion (entry source) source - (length : ℂ) * direction source‖ ≤ length / 64 ∧
        ‖secondDipoleSeparation motion (entry source) source - (length : ℂ) * (-direction source)‖ ≤ length / 64 ∧
        (3 / 4 : ℝ) * length * initialDistance source ≤
          (Complex.I * star (direction source) * (firstDipoleCenter motion (entry source) source -
            secondDipoleCenter motion (entry source) source)).re ∧
        ‖firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source‖ ≤
          (5 / 4 : ℝ) * length * initialDistance source) →
      (∀ source : Fin count, index.val < source.val → ∀ time ∈ Icc 0 (entry source),
        (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
          quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
            extent * changed.length (source.val + 1)) ∧
        (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
          extent * changed.length (source.val + 1))) →
      ∀ magnitude : Fin count → ℝ,
      let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
        ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
        ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
      (∀ source : Fin count, index.val < source.val → 0 ≤ magnitude source ∧ ∀ time ∈ Icc 0 (entry source),
        sharpState source time ≤ magnitude source * Real.exp (sourceRate * changed.omega (source.val + 1) * (time - entry source))) →
      (∀ source : Fin count, index.val < source.val → magnitude source ≤ magnitudeMax) →
      (∀ source : Fin count, index.val < source.val → initialDistance source ≤ distanceMax) →
      (∀ source : Fin count, index.val < source.val → ∀ time ∈ Icc 0 (entry source), ∀ patch,
        motion.domain time source patch ⊆ Metric.closedBall (quadrupoleCenter motion time source)
          (extent * changed.length (source.val + 1))) →
      ∀ actualTime : ℕ → ℝ, (∀ source : Fin count, actualTime (source.val + 1) = entry source) →
      |actualTime (index.val + 2) - changed.predictedTime sectionTime count (index.val + 2)| ≤
        timingError / changed.omega (index.val + 2) →
      (∀ source : Fin count, index.val < source.val →
        |actualTime (source.val + 1) - changed.predictedTime sectionTime count (source.val + 1)| ≤
          timingError / changed.omega (source.val + 1)) →
      (∀ source : Fin count, index.val < source.val → entry source ≤ entry ⟨index.val + 1, nonterminal⟩) →
      entry ⟨index.val + 1, nonterminal⟩ ≤ 1 / 2 →
      (∀ source : Fin count, index.val < source.val →
        2 * (2 * Real.sqrt 2 * changed.omega (index.val + 1)) ≤ sourceRate * changed.omega (source.val + 1)) →
      let drive : Fin count := ⟨index.val + 1, nonterminal⟩
      ∀ outgoingPhase : ℝ, ∀ sourceWinding : ℤ,
      direction drive = Complex.exp (Complex.I * (outgoingPhase : ℂ)) →
      |outgoingPhase - dipoleAngle (drive.val + 1) + changed.omega (drive.val + 1) *
        (entry drive - changed.predictedTime sectionTime count (drive.val + 1)) -
          (sourceWinding : ℝ) * Real.pi| ≤ phaseTolerance →
      2048 ≤ initialDistance drive →
      20 * initialError + 83200 / (initialDistance drive) ^ 2 ≤ (min ((1 / 32 : ℝ) / 4) 1) / 5120 →
      ‖firstDipoleSeparation motion (entry drive) drive -
        (changed.length (drive.val + 1) : ℂ) * direction drive‖ ≤ initialError * changed.length (drive.val + 1) →
      ‖secondDipoleSeparation motion (entry drive) drive -
        (changed.length (drive.val + 1) : ℂ) * (-direction drive)‖ ≤ initialError * changed.length (drive.val + 1) →
      let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
      let origin := entry ⟨index.val + 1, nonterminal⟩
      let finish := origin + Real.log (endpoint / changed.seed (index.val + 1)) / growth
      0 < finish ∧ 0 < finish - origin ∧ finish - origin < 1 / 4 ∧
      512 ≤ growth * (finish - origin) ∧
      changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) = endpoint ∧
      finish < 3 / 4 ∧ finish ≤ path.stop ∧
      endpoint / 2 ≤ (referenceStraightenedShape motion graph coordinate index finish -
        referenceStraightenedShape prepared.reference graph coordinate index finish).1 ∧
      (∃ hit : ℝ, origin < hit ∧ hit ≤ finish ∧
        (referenceStraightenedShape motion graph coordinate index hit -
          referenceStraightenedShape prepared.reference graph coordinate index hit).1 = coordinate (orbitUnstableShape orbit incomingTime) ∧
        (∀ time : ℝ, 0 ≤ time → time < hit →
          (referenceStraightenedShape motion graph coordinate index time -
            referenceStraightenedShape prepared.reference graph coordinate index time).1 < coordinate (orbitUnstableShape orbit incomingTime)) ∧
        (∀ current : Fin count, current.val ≤ index.val → ∀ time ∈ Icc 0 hit,
          |unstableShape motion time current| + |stableShape motion time current| ≤ radius) ∧
        ∃ rotation : ℂ,
          halfDiagonalMatchingRotation (positiveHalfDiagonal motion hit index) (orbit.positive incomingTime) = rotation ∧
          ‖rotation‖ = 1 ∧
          ‖cascadeNormalizedPointPositions changed motion index hit rotation 0 -
            centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ < matchingAccuracy) ∧
      (∀ time ∈ Icc 0 finish, ∀ current : Fin count, current.val ≤ index.val →
        |unstableShape motion time current| + |stableShape motion time current| ≤ 1 / 4) ∧
      (∃ lift : Fin 2 → ℝ → ℝ,
      (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift side time : ℂ))) ∧
      let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
      let state := fun time => prepared.finiteCoordinateSize graph coordinate lift index time + raw time
      let sharp := fun time => prepared.rawSourceCenteredState time index +
        ‖relativeNormalizedFirstMoment changed motion prepared.reference index time‖ +
        ‖quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index‖ / changed.location (index.val + 1) + raw time
      let forcing := fun time => prepared.finiteCoordinateForeignForcing index time + prepared.physicalForeignSourceForcing index time
      ContinuousOn state (Icc 0 finish) ∧ state 0 = 0 ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * state time) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * forcing time) volume 0 finish ∧
      ∀ time ∈ Icc 0 finish,
        state time ≤ currentMagnitude *
          changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) ∧
        sharp time ≤ currentMagnitude *
          changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) ∧
      ∃ lift : Fin count → Fin 2 → ℝ → ℝ,
        (∀ receiver side, Continuous (lift receiver side) ∧ lift receiver side 0 = phase (receiver.val + 1)) ∧
        (∀ receiver : Fin count, receiver.val < index.val → ∀ side, ∀ time ∈ Icc 0 finish,
          positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
            (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
              Complex.exp (Complex.I * (lift receiver side time : ℂ))) ∧
        ∀ time ∈ Icc 0 finish, ∀ receiver : Fin count, receiver.val < index.val →
          prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
            ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch ≤ precision := by
  classical
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, firstThreshold, firstThresholdPositive, firstEighth,
    compatible, firstCap, firstCapPositive, firstFactors⟩ := exists_uniform_actual_positive_first_hit
  obtain ⟨matchThreshold, matchThresholdPositive, _, matchCap, matchCapPositive, matchFactors⟩ :=
    exists_uniform_actual_accurate_straightened_hit_match graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative orbit normalized (compatible orbit normalized)
  let thresholdMax := min firstThreshold matchThreshold
  let rawCap := min firstCap matchCap
  have thresholdFirst : thresholdMax ≤ firstThreshold := min_le_left _ _
  have thresholdMatch : thresholdMax ≤ matchThreshold := min_le_right _ _
  have capFirst : rawCap ≤ firstCap := min_le_left _ _
  have capMatch : rawCap ≤ matchCap := min_le_right _ _
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, lt_min firstThresholdPositive matchThresholdPositive,
    thresholdFirst.trans firstEighth, compatible, rawCap, lt_min firstCapPositive matchCapPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨currentMagnitude, currentOne, firstRoot, firstRootEight, firstEndpoint, firstEndpointPositive,
    firstEndpointOne, firstParameters⟩ := firstFactors factorPositive factorSmall
  have currentNonnegative : 0 ≤ currentMagnitude := zero_le_one.trans currentOne
  obtain ⟨matchRadius, matchRadiusPositive, matchRadiusQuarter, matchRoot, _, matchMagnitudes⟩ :=
    matchFactors factor factorPositive factorSmall
  obtain ⟨matchEndpoint, matchEndpointPositive, _, matchIncoming⟩ :=
    matchMagnitudes currentMagnitude currentNonnegative currentMagnitude currentNonnegative
  obtain ⟨physicalPrecision, physicalPrecisionPositive, refinePhysical⟩ :=
    exists_uniform_actual_full_state_physical_refinement graphAnalytic.contDiffAt coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative matchRadiusPositive
  let rootMin := max firstRoot matchRoot
  let endpointMax := min firstEndpoint (min matchEndpoint (physicalPrecision / (currentMagnitude + 1)))
  have endpointMaxPositive : 0 < endpointMax := by dsimp only [endpointMax]; positivity
  have endpointMaxFirst : endpointMax ≤ firstEndpoint := min_le_left _ _
  have endpointMaxMatch : endpointMax ≤ matchEndpoint := (min_le_right _ _).trans (min_le_left _ _)
  have endpointMaxPhysical : endpointMax ≤ physicalPrecision / (currentMagnitude + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨currentMagnitude, currentOne, matchRadius, matchRadiusPositive, matchRadiusQuarter,
    rootMin, firstRootEight.trans (le_max_left _ _), endpointMax, endpointMaxPositive,
    endpointMaxFirst.trans firstEndpointOne, ?_⟩
  intro endpoint endpointPositive endpointBound
  have targetLimit : Tendsto (fun time => coordinate (orbitUnstableShape orbit time)) atBot (𝓝 0) := by
    have actual := coordinateSmooth.continuousAt.tendsto.comp
      (continuous_fst.continuousAt.tendsto.comp (normalizedSeparatingOrbit_shape_tendsto_zero orbit normalized))
    simpa only [coordinateZero] using actual
  filter_upwards [matchIncoming,
    normalizedSeparatingOrbit_eventually_positive_coordinate coordinateZero coordinateDerivative orbit normalized,
    targetLimit.eventually (eventually_lt_nhds (half_pos endpointPositive)),
    eventually_lt_atBot sectionTime] with incomingTime matchAt targetPositive targetSmall incomingBefore
  refine ⟨incomingBefore, targetPositive, targetSmall.le, ?_⟩
  intro matchingAccuracy matchingPositive precision precisionPositive extent magnitudeMax distanceMax sourceRate
    extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive sourceRateSmall
    initialError initialErrorSmall phaseTolerance phaseNonnegative
  let selectedPrecision := min precision physicalPrecision
  have selectedPositive : 0 < selectedPrecision := lt_min precisionPositive physicalPrecisionPositive
  obtain ⟨firstRatio, firstRatioTwo, firstScales⟩ := firstParameters endpoint endpointPositive
    (endpointBound.trans endpointMaxFirst) (coordinate (orbitUnstableShape orbit incomingTime)) targetPositive targetSmall.le
    selectedPrecision selectedPositive extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative
    distanceNonnegative sourceRatePositive sourceRateSmall initialError initialErrorSmall phaseTolerance phaseNonnegative
  obtain ⟨matchRatio, _, matchScales⟩ := matchAt matchingAccuracy matchingPositive extent magnitudeMax distanceMax sourceRate
    extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  let ratioMin := max firstRatio (max matchRatio (4 * Real.sqrt 2 / sourceRate))
  refine ⟨ratioMin, firstRatioTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound boundaryConstant timingError boundaryOne timingNonnegative
    phaseBudget controlledSeparation
  have firstRatioLarge : firstRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have matchRatioLarge : matchRatio ≤ scales.ratio := (le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge)
  have rateRatio : 4 * Real.sqrt 2 / sourceRate ≤ scales.ratio :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge)
  have ratioBound : 2 ≤ scales.ratio := firstRatioTwo.trans firstRatioLarge
  have rateProduct : 4 * Real.sqrt 2 ≤ sourceRate * scales.ratio := by
    have bound := (div_le_iff₀ sourceRatePositive).mp rateRatio
    simpa only [mul_comm] using bound
  have ratioSeparation : (2 * Real.sqrt 2 + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) := by
    have sqrtNonnegative := Real.sqrt_nonneg (2 : ℝ)
    nlinarith only [rateProduct, controlledSeparation, sqrtNonnegative]
  have globalGap : 4 * Real.sqrt 2 ≤ sourceRate * scales.ratio ^ 2 := by
    have sqBound : scales.ratio ≤ scales.ratio ^ 2 := by nlinarith only [ratioBound]
    exact rateProduct.trans (mul_le_mul_of_nonneg_left sqBound sourceRatePositive.le)
  have firstRootLarge : firstRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have matchRootLarge : matchRoot ≤ scaleRoot := (le_max_right _ _).trans rootLarge
  filter_upwards [firstScales scales scaleRoot firstRootLarge amplitudeIdentity firstRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdFirst)
      orbit sectionTime boundaryConstant timingError boundaryOne timingNonnegative sectionPositive phaseBudget controlledSeparation,
    matchScales scales scaleRoot matchRootLarge amplitudeIdentity matchRatioLarge alphaPositive alphaSmall ratioPower globalGap
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdMatch)
      sectionTime boundaryConstant timingError boundaryOne timingNonnegative ratioSeparation,
    refinePhysical scales ratioBound alphaPositive referenceConstant referenceNonnegative,
    eventually_gt_atTop (0 : ℝ)] with frequency first matching physical frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path prescribed index nonterminal driveNonterminal
    entry initialDistance direction
  dsimp only
  intro entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming
    sourceTiming timeOrder originBound sourceRates outgoingPhase sourceWinding directionIdentity phaseSmall distanceLarge
    numericBudget firstInitial secondInitial
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let origin := entry ⟨index.val + 1, nonterminal⟩
  let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  let finish := origin + Real.log (endpoint / changed.seed (index.val + 1)) / growth
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time current patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  have sizeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateSize graph coordinate = prepared.finiteCoordinateSize graph coordinate := rfl
  have payload := first count phase dipoleAngle (prepared.enlargeCap capFirst) path prescribed index nonterminal driveNonterminal
    entry initialDistance direction entries extents magnitude (by simpa only [rawInvariant, centeredInvariant] using sourceProfiles)
    magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder originBound sourceRates
    outgoingPhase sourceWinding directionIdentity phaseSmall distanceLarge numericBudget firstInitial secondInitial
  dsimp only at payload
  simp only [rawInvariant, centeredInvariant, sizeInvariant] at payload
  obtain ⟨finishPositive, elapsedPositive, elapsedSmall, elapsedLarge, exposure, finishSmall, finishAvailable,
    unstableLower, hitData, weakPhysical, targetData, coarseLift, coarseLiftProperties, coarseLiftPolar, coarseFull⟩ := payload
  obtain ⟨hit, hitAfter, hitBefore, hitIdentity, leastHit⟩ := hitData
  have savedTarget := targetData
  obtain ⟨lift, liftProperties, liftPolar, stateContinuous, stateZero, stateI, forcingI, targetBounds⟩ := targetData
  have originNonnegative : 0 ≤ origin := (entries ⟨index.val + 1, nonterminal⟩ (by simp)).1
  have hitPositive : 0 < hit := lt_of_le_of_lt originNonnegative hitAfter
  have hitInside : hit ∈ Icc 0 path.stop := ⟨hitPositive.le, hitBefore.trans finishAvailable⟩
  have finishInside : finish ∈ Icc 0 path.stop := ⟨finishPositive.le, finishAvailable⟩
  have growthPositive : 0 < growth := by
    have omegaPositive := changed.omega_pos frequencyPositive
      (by change 0 < scales.ratio; linarith only [ratioBound]) (index.val + 1)
    dsimp only [growth]; positivity
  have seedPositive : 0 < changed.seed (index.val + 1) := changed.seed_pos frequencyPositive
    (by change 0 < scales.ratio; linarith only [ratioBound]) _
  have exposureAt (time : ℝ) (before : time ≤ finish) :
      changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) ≤ endpoint := by
    rw [← exposure]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right before origin) growthPositive.le)) seedPositive.le
  have currentFullSmall (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.finiteCoordinateSize graph coordinate lift index time + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
        physicalPrecision := by
    have scaled := mul_le_mul_of_nonneg_left (endpointBound.trans endpointMaxPhysical)
      (show 0 ≤ currentMagnitude + 1 by positivity)
    have identity : (currentMagnitude + 1) * (physicalPrecision / (currentMagnitude + 1)) = physicalPrecision := by field_simp
    rw [identity] at scaled
    have magnitudeBound : currentMagnitude * endpoint ≤ physicalPrecision := by nlinarith only [scaled, endpointPositive]
    calc
      _ ≤ currentMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) := (targetBounds time inside).1
      _ = currentMagnitude * (changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) := by ring
      _ ≤ currentMagnitude * endpoint := mul_le_mul_of_nonneg_left (exposureAt time inside.2) currentNonnegative
      _ ≤ physicalPrecision := magnitudeBound
  have physicalAll (current : Fin count) (before : current.val ≤ index.val) (time : ℝ) (inside : time ∈ Icc 0 hit) :
      |unstableShape motion time current| + |stableShape motion time current| ≤ matchRadius := by
    have subset : time ∈ Icc 0 finish := ⟨inside.1, inside.2.trans hitBefore⟩
    rcases lt_or_eq_of_le before with earlier | equal
    · have refined := physical prepared path factorPositive current (by omega) finish finishInside
        (fun time inside => weakPhysical time inside current before) (coarseLift current) (by
          intro time inside
          exact (coarseFull time inside current earlier).trans (min_le_right precision physicalPrecision))
      exact (refined time subset).le
    · have same : current = index := Fin.ext equal
      subst current
      exact (physical prepared path factorPositive index nonterminal finish finishInside
        (fun time inside => weakPhysical time inside index le_rfl) lift currentFullSmall time subset).le
  have actualMatch := matching count phase dipoleAngle (prepared.enlargeCap capMatch) path index nonterminal
    entry initialDistance direction entries extents magnitude (by simpa only [rawInvariant, centeredInvariant] using sourceProfiles)
    magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder hit hitInside physicalAll
    lift liftProperties (fun side time inside => liftPolar side time ⟨inside.1, inside.2.trans hitBefore⟩) sourceRates
    (by
      intro time inside
      simpa only [rawInvariant, sizeInvariant] using (targetBounds time ⟨inside.1, inside.2.trans hitBefore⟩).1)
    (by
      intro time inside
      simpa only [rawInvariant, centeredInvariant] using (targetBounds time ⟨inside.1, inside.2.trans hitBefore⟩).2)
    hitAfter.le ((exposureAt hit hitBefore).trans (endpointBound.trans endpointMaxMatch)) hitIdentity
  refine ⟨finishPositive, elapsedPositive, elapsedSmall, elapsedLarge, exposure, finishSmall, finishAvailable,
    unstableLower, ⟨hit, hitAfter, hitBefore, hitIdentity, leastHit, physicalAll, ?_⟩,
    weakPhysical, savedTarget, coarseLift, coarseLiftProperties, coarseLiftPolar, ?_⟩
  · exact ⟨_, actualMatch⟩
  · intro time inside current earlier
    exact (coarseFull time inside current earlier).trans (min_le_left precision physicalPrecision)

end EulerNonuniqueness.Paper
