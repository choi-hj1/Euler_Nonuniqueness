import EulerNonuniqueness.Section5.CascadeActualFirstSeparation
import EulerNonuniqueness.Section5.CascadeCompactSlowSourceProfile

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_outgoing_sharp_profile
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (sectionTime initialError : ℝ) (modelDerivative : ℝ → ℝ)
    (sectionPositive : 0 < sectionTime) (errorPositive : 0 < initialError) (errorSmall : initialError ≤ 1 / 64)
    (radiusLarge : 512 ≤ separationRadius orbit sectionTime)
    (transverse : ∀ time ∈ Icc (sectionTime - 1) (sectionTime + 1),
      HasDerivAt (separationRadius orbit) (modelDerivative time) time ∧ 1 ≤ modelDerivative time)
    (earlierMargin : ∀ time ≤ sectionTime - 1,
      separationRadius orbit time ≤ separationRadius orbit sectionTime - 1)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ initialError / 2)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re)
    {separationAccuracy : ℝ} (separationAccuracyPositive : 0 < separationAccuracy)
    (sourceRate : ℝ) (sourceRatePositive : 0 < sourceRate) (sourceRateSmall : sourceRate < 1 / 8) :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ),
      ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      (∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
        2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
          centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖) →
      ∃ currentMagnitude ≥ (1 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      ∃ rootMin ≥ (8 : ℝ), ∃ passageExtent ≥ (4 : ℝ), ∃ endpointMax > (0 : ℝ),
      endpointMax ≤ 1 ∧ ∀ endpoint : ℝ, 0 < endpoint → endpoint ≤ endpointMax →
      ∀ᶠ incomingTime : ℝ in atBot,
      incomingTime + 1 < sectionTime ∧ 0 < coordinate (orbitUnstableShape orbit incomingTime) ∧
      coordinate (orbitUnstableShape orbit incomingTime) ≤ endpoint / 2 ∧
      ∃ stageTolerance > (0 : ℝ), ∃ historyMagnitude ≥ (0 : ℝ), ∀ matchingAccuracy : ℝ, 0 < matchingAccuracy → ∀ precision : ℝ, 0 < precision →
      ∀ extent magnitudeMax distanceMax : ℝ,
      1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax →
      ∀ phaseTolerance : ℝ, 0 ≤ phaseTolerance →
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
      (∀ other : Fin count, index.val < other.val → other.val + 1 < count →
        ∃ previousHit ∈ Icc 0 (entry other), ∃ previousRotation : ℂ, ‖previousRotation‖ = 1 ∧
          ‖cascadeNormalizedPointPositions changed motion other previousHit previousRotation 0 -
            centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ stageTolerance) →
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
            centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ < min stageTolerance matchingAccuracy ∧
          let omega := changed.omega (index.val + 1)
          let length := changed.length (index.val + 1)
          let direction := rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
          let compactEndpoint := hit + (sectionTime + 1 - incomingTime) / omega
          compactEndpoint ≤ path.stop ∧ ‖direction‖ = 1 ∧
          ∃ contact ∈ Icc (hit + (sectionTime - incomingTime - 1) / omega) compactEndpoint,
            FirstSeparationTime changed orbit sectionTime motion index contact ∧
            (∀ earlier ∈ Ico 0 contact, pairCenterDistance motion earlier index < separationRadius orbit sectionTime * length) ∧
            |contact - (hit + (sectionTime - incomingTime) / omega)| ≤ 2 * separationAccuracy / omega ∧
            ‖firstDipoleCenter motion contact index - secondDipoleCenter motion contact index‖ = length * separationRadius orbit sectionTime ∧
            ‖firstDipoleSeparation motion contact index - (length : ℂ) * direction‖ ≤ initialError * length ∧
            ‖secondDipoleSeparation motion contact index - (length : ℂ) * (-direction)‖ ≤ initialError * length ∧
            (3 / 4 : ℝ) * length * separationRadius orbit sectionTime ≤
              (Complex.I * star direction * (firstDipoleCenter motion contact index - secondDipoleCenter motion contact index)).re ∧
            ‖firstDipoleCenter motion contact index - secondDipoleCenter motion contact index‖ ≤
              (5 / 4 : ℝ) * length * separationRadius orbit sectionTime ∧
            (∀ time ∈ Icc 0 contact, ∀ patch : Fin 4,
              ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤ passageExtent * length ∧
              ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index patch -
                quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index‖ ≤ passageExtent * length ∧
              motion.domain time index patch ⊆ Metric.closedBall (quadrupoleCenter motion time index) (passageExtent * length) ∧
              prepared.referenceWitness.trajectory.movingFamily.patchMotion.domain time index patch ⊆
                Metric.closedBall (quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index)
                  (passageExtent * length)) ∧
            (∀ time ∈ Icc 0 contact, sharpState index time ≤
              historyMagnitude * Real.exp (sourceRate * omega * (time - contact)))) ∧
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
    coordinateDerivative, chartConstant, chartOne, stageThreshold, stageThresholdPositive, stageEighth,
    compatible, stageCap, stageCapPositive, stageFactors⟩ :=
    exists_uniform_actual_first_separation orbit normalized sectionTime initialError modelDerivative sectionPositive
      errorPositive errorSmall radiusLarge transverse earlierMargin separationClose outgoing separationAccuracyPositive
  obtain ⟨slowCap, slowCapPositive, slowFactors⟩ := exists_uniform_actual_compact_slow_source_profile
  let rawCap := min stageCap slowCap
  have capStage : rawCap ≤ stageCap := min_le_left _ _
  have capSlow : rawCap ≤ slowCap := min_le_right _ _
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, stageThreshold, stageThresholdPositive, stageEighth, compatible,
    rawCap, lt_min stageCapPositive slowCapPositive, ?_⟩
  intro factor factorPositive factorSmall referenceSeparated
  obtain ⟨currentMagnitude, currentOne, radius, radiusPositive, radiusQuarter, rootMin, rootEight,
    passageExtent, passageFour, endpointMax, endpointMaxPositive, endpointMaxOne, stageParameters⟩ :=
    stageFactors factorPositive factorSmall referenceSeparated
  have currentNonnegative : 0 ≤ currentMagnitude := zero_le_one.trans currentOne
  have passageOne : 1 ≤ passageExtent := (by norm_num : (1 : ℝ) ≤ 4).trans passageFour
  refine ⟨currentMagnitude, currentOne, radius, radiusPositive, radiusQuarter, rootMin, rootEight,
    passageExtent, passageFour, endpointMax, endpointMaxPositive, endpointMaxOne, ?_⟩
  intro endpoint endpointPositive endpointBound
  filter_upwards [stageParameters endpoint endpointPositive endpointBound] with incomingTime stageAt
  obtain ⟨sectionAfter, targetPositive, targetSmall, stageTolerance, stageTolerancePositive, stageAccuracy⟩ := stageAt
  let span := sectionTime + 1 - incomingTime
  have spanPositive : 0 < span := by dsimp only [span]; linarith only [sectionAfter]
  obtain ⟨historyMagnitude, historyNonnegative, slowScales⟩ := slowFactors factor factorPositive factorSmall
    passageExtent passageOne span spanPositive.le sourceRate sourceRatePositive sourceRateSmall currentMagnitude currentNonnegative
  refine ⟨sectionAfter, targetPositive, targetSmall, stageTolerance, stageTolerancePositive,
    historyMagnitude, historyNonnegative, ?_⟩
  intro matchingAccuracy matchingPositive precision precisionPositive extent magnitudeMax distanceMax
    extentOne magnitudeNonnegative distanceNonnegative phaseTolerance phaseNonnegative
  obtain ⟨stageRatio, stageRatioTwo, stageScales⟩ := stageAccuracy matchingAccuracy matchingPositive precision precisionPositive
    extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive sourceRateSmall
    phaseTolerance phaseNonnegative
  let ratioMin := max stageRatio 16
  refine ⟨ratioMin, stageRatioTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound boundaryConstant timingError boundaryOne timingNonnegative
    phaseBudget controlledSeparation
  have stageRatioLarge : stageRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioSixteen : 16 ≤ scales.ratio := (le_max_right _ _).trans ratioLarge
  have ratioBound : 2 ≤ scales.ratio := stageRatioTwo.trans stageRatioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans stageEighth
  filter_upwards [stageScales scales scaleRoot rootLarge amplitudeIdentity stageRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound boundaryConstant timingError
      boundaryOne timingNonnegative phaseBudget controlledSeparation,
    slowScales scales amplitudePositive ratioSixteen alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    eventually_gt_atTop (0 : ℝ)] with frequency stage slow frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path prescribed index nonterminal driveNonterminal
    entry initialDistance direction
  dsimp only
  intro entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming
    sourceTiming timeOrder originBound sourceRates previousMatches outgoingPhase sourceWinding directionIdentity phaseSmall
    distanceLarge numericBudget firstInitial secondInitial
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let origin := entry ⟨index.val + 1, nonterminal⟩
  let omega := changed.omega (index.val + 1)
  let growth := 2 * Real.sqrt 2 * omega
  let finish := origin + Real.log (endpoint / changed.seed (index.val + 1)) / growth
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have growthPositive : 0 < growth := by dsimp only [growth]; positivity
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time current patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  have sizeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateSize graph coordinate = prepared.finiteCoordinateSize graph coordinate := rfl
  have payload := stage count phase dipoleAngle (prepared.enlargeCap capStage) path prescribed index nonterminal driveNonterminal
    entry initialDistance direction entries extents magnitude (by simpa only [rawInvariant, centeredInvariant] using sourceProfiles)
    magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder originBound sourceRates previousMatches
    outgoingPhase sourceWinding directionIdentity phaseSmall distanceLarge numericBudget firstInitial secondInitial
  dsimp only at payload
  simp only [rawInvariant, centeredInvariant, sizeInvariant] at payload
  obtain ⟨finishPositive, elapsedPositive, elapsedSmall, elapsedLarge, exposure, finishSmall, finishAvailable,
    unstableLower, hitData, weakPhysical, targetData, coarseLift, coarseLiftProperties, coarseLiftPolar, coarseFull⟩ := payload
  obtain ⟨hit, hitAfter, hitBefore, hitIdentity, leastHit, hitPhysical, rotation, canonical, rotationNorm, matchingClose,
    compactAvailable, directionNorm, contact, contactInside, firstContact, earlierStrict, timing, pairNorm,
    firstEntry, secondEntry, projection, upper, contactDomains⟩ := hitData
  have savedTarget := targetData
  obtain ⟨lift, liftProperties, liftPolar, stateContinuous, stateZero, stateI, forcingI, targetBounds⟩ := targetData
  have originNonnegative : 0 ≤ origin := (entries ⟨index.val + 1, nonterminal⟩ (by simp)).1
  have hitPositive : 0 < hit := lt_of_le_of_lt originNonnegative hitAfter
  have hitInside : hit ∈ Icc 0 path.stop := ⟨hitPositive.le, hitBefore.trans finishAvailable⟩
  have contactAfter : hit ≤ contact := by
    have lower : hit ≤ hit + (sectionTime - incomingTime - 1) / omega :=
      le_add_of_nonneg_right (div_nonneg (by linarith only [sectionAfter]) omegaPositive.le)
    exact lower.trans contactInside.1
  have contactBefore : contact ≤ path.stop := contactInside.2.trans compactAvailable
  have spanBound : omega * (contact - hit) ≤ span := by
    have scaled := mul_le_mul_of_nonneg_left (sub_le_sub_right contactInside.2 hit) omegaPositive.le
    have identity : omega * (hit + (sectionTime + 1 - incomingTime) / omega - hit) = span := by
      dsimp only [span]
      field_simp
      ring
    rw [identity] at scaled
    exact scaled
  have exposureHit : changed.seed (index.val + 1) * Real.exp (growth * (hit - origin)) ≤ 1 := by
    have exponent := mul_le_mul_of_nonneg_left (sub_le_sub_right hitBefore origin) growthPositive.le
    have bounded := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponent)
      (changed.seed_pos frequencyPositive ratioPositive (index.val + 1)).le
    exact bounded.trans (by rw [exposure]; exact endpointBound.trans endpointMaxOne)
  have slowProfile := slow count phase dipoleAngle (prepared.enlargeCap capSlow) path index hit hitInside
    contact ⟨contactAfter, contactBefore⟩ spanBound
    (fun time inside patch => (contactDomains time ⟨hitPositive.le.trans inside.1, inside.2⟩ patch).1)
    (by
      intro time inside patch
      have bound := (contactDomains time ⟨hitPositive.le.trans inside.1, inside.2⟩ patch).2.1
      change ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index‖ ≤
          passageExtent * changed.length (index.val + 1) at bound
      change ‖patchCentroid prepared.reference time index patch - quadrupoleCenter prepared.reference time index‖ ≤
        passageExtent * changed.length (index.val + 1)
      simpa only [← prepared.referenceIdentity] using bound)
    origin (by
      intro time inside
      simpa only [rawInvariant, centeredInvariant] using (targetBounds time ⟨inside.1, inside.2.trans hitBefore⟩).2)
    exposureHit
  simp only [rawInvariant, centeredInvariant] at slowProfile
  refine ⟨finishPositive, elapsedPositive, elapsedSmall, elapsedLarge, exposure, finishSmall, finishAvailable,
    unstableLower, ⟨hit, hitAfter, hitBefore, hitIdentity, leastHit, hitPhysical, rotation, canonical, rotationNorm, matchingClose,
      compactAvailable, directionNorm, contact, contactInside, firstContact, earlierStrict, timing, pairNorm,
      firstEntry, secondEntry, projection, upper, contactDomains, slowProfile⟩,
    weakPhysical, savedTarget, coarseLift, coarseLiftProperties, coarseLiftPolar, coarseFull⟩

end EulerNonuniqueness.Paper
