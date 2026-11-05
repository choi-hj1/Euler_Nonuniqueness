import EulerNonuniqueness.Section5.CascadeTerminalActualFirstSeparation
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

theorem exists_uniform_actual_terminal_outgoing_sharp_profile (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) (sectionTime initialError : ℝ) (modelDerivative : ℝ → ℝ)
    (sectionPositive : 0 < sectionTime)
    (errorPositive : 0 < initialError) (errorSmall : initialError ≤ 1 / 64)
    (radiusLarge : 2048 ≤ separationRadius orbit sectionTime)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ initialError / 2)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re)
    (transverse : ∀ time ∈ Icc (sectionTime - 1) (sectionTime + 1),
      HasDerivAt (separationRadius orbit) (modelDerivative time) time ∧ 1 ≤ modelDerivative time)
    (earlierMargin : ∀ time ≤ sectionTime - 1,
      separationRadius orbit time ≤ separationRadius orbit sectionTime - 1)
    {separationAccuracy : ℝ} (separationAccuracyPositive : 0 < separationAccuracy)
    {coefficient : ℝ} (coefficientPositive : 0 < coefficient) (coefficientSmall : coefficient < 1 / 8)
    (numericBudget : 20 * initialError + 83200 / (separationRadius orbit sectionTime) ^ 2 ≤
      min ((1 / 8 : ℝ) / 4) 1 / 5120) :
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
      ∃ incomingMagnitude ≥ (0 : ℝ),
      ∃ rootMin ≥ (8 : ℝ), ∃ passageExtent ≥ (4 : ℝ), ∃ endpointMax > (0 : ℝ),
      endpointMax ≤ 1 ∧ ∀ endpoint : ℝ, 0 < endpoint → endpoint ≤ endpointMax →
      ∀ᶠ incomingTime : ℝ in atBot,
      incomingTime + 1 < sectionTime ∧ 0 < coordinate (orbitUnstableShape orbit incomingTime) ∧
      coordinate (orbitUnstableShape orbit incomingTime) ≤ endpoint / 2 ∧
      ∃ matchingTolerance > (0 : ℝ), ∃ historyMagnitude ≥ (0 : ℝ),
      ∀ requestedMatchingAccuracy > (0 : ℝ),
      ∀ coarsePrecision > (0 : ℝ),
      ∃ ratioMin ≥ (2 : ℝ),
      ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
      ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
      ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
      ∀ boundaryConstant : ℝ, 1 ≤ boundaryConstant →
      (2 * Real.sqrt 2 + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ index : Fin count,
      ∀ source : Fin count, index.val + 1 = source.val → source.val + 1 = count →
      PrescribedCascadePhases {scales with frequency := frequency} orbit sectionTime count phase dipoleAngle →
      let changed : Scales := {scales with frequency := frequency}
      let motion := prepared.trajectory.movingFamily.patchMotion
      let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
      let finish := Real.log (endpoint / changed.seed (index.val + 1)) / growth
      0 < finish ∧ finish < 1 / 4 ∧ 256 ≤ growth * finish ∧
      changed.seed (index.val + 1) * Real.exp (growth * finish) = endpoint ∧
      finish ≤ path.stop ∧
      endpoint / 2 ≤ (referenceStraightenedShape motion graph coordinate index finish -
        referenceStraightenedShape prepared.reference graph coordinate index finish).1 ∧
      (∃ hit : ℝ, 0 < hit ∧ hit ≤ finish ∧
        (referenceStraightenedShape motion graph coordinate index hit -
          referenceStraightenedShape prepared.reference graph coordinate index hit).1 =
          coordinate (orbitUnstableShape orbit incomingTime) ∧
        (∀ time : ℝ, 0 ≤ time → time < hit →
          (referenceStraightenedShape motion graph coordinate index time -
            referenceStraightenedShape prepared.reference graph coordinate index time).1 <
            coordinate (orbitUnstableShape orbit incomingTime)) ∧
        (∀ current : Fin count, current.val ≤ index.val → ∀ time ∈ Icc 0 hit,
          |unstableShape motion time current| + |stableShape motion time current| ≤ 1 / 4) ∧
        (∀ time ∈ Icc 0 hit,
          prepared.rawSourceCenteredState time index +
            ‖relativeNormalizedFirstMoment changed motion prepared.reference index time‖ +
            ‖quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index‖ /
              changed.location (index.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
            incomingMagnitude * changed.seed (index.val + 1) * Real.exp (growth * time)) ∧
        changed.seed (index.val + 1) * Real.exp (growth * hit) ≤ 1 ∧
        ∃ rotation : ℂ,
          halfDiagonalMatchingRotation (positiveHalfDiagonal motion hit index) (orbit.positive incomingTime) = rotation ∧
          ‖rotation‖ = 1 ∧
          ‖cascadeNormalizedPointPositions changed motion index hit rotation 0 -
            centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ < min matchingTolerance requestedMatchingAccuracy ∧
          let omega := changed.omega (index.val + 1)
          let length := changed.length (index.val + 1)
          let direction := rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
          let compactEndpoint := hit + (sectionTime + 1 - incomingTime) / omega
          compactEndpoint ≤ path.stop ∧ ‖direction‖ = 1 ∧
          ∃ contact ∈ Icc (hit + (sectionTime - incomingTime - 1) / omega) compactEndpoint,
            contact ∈ Icc hit path.stop ∧
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
            (∀ time ∈ Icc 0 contact,
              prepared.rawSourceCenteredState time index +
                ‖relativeNormalizedFirstMoment changed motion prepared.reference index time‖ +
                ‖quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index‖ /
                  changed.location (index.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
                historyMagnitude * Real.exp (coefficient * omega * (time - contact))) ∧
            ∀ time ∈ Icc 0 contact, ∀ patch : Fin 4,
              ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤ passageExtent * length ∧
              ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index patch -
                quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index‖ ≤ passageExtent * length ∧
              motion.domain time index patch ⊆ Metric.closedBall (quadrupoleCenter motion time index) (passageExtent * length) ∧
              prepared.referenceWitness.trajectory.movingFamily.patchMotion.domain time index patch ⊆
                Metric.closedBall (quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index)
                  (passageExtent * length)) ∧
      (∃ lift : Fin 2 → ℝ → ℝ,
        (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
        (∀ side, ∀ time ∈ Icc 0 finish,
          positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
            (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
              Complex.exp (Complex.I * (lift side time : ℂ))) ∧
        ∀ time ∈ Icc 0 finish,
          prepared.finiteCoordinateSize graph coordinate lift index time +
            ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
              incomingMagnitude * changed.seed (index.val + 1) * Real.exp (growth * time)) ∧
      ∃ coarseLift : Fin count → Fin 2 → ℝ → ℝ,
        (∀ current side, Continuous (coarseLift current side) ∧
          coarseLift current side 0 = phase (current.val + 1)) ∧
        (∀ current : Fin count, current.val < index.val → ∀ side, ∀ time ∈ Icc 0 finish,
          positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time current =
            (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time current‖ : ℂ) *
              Complex.exp (Complex.I * (coarseLift current side time : ℂ))) ∧
        ∀ time ∈ Icc 0 finish, ∀ current : Fin count, current.val < index.val →
          prepared.finiteCoordinateSize graph coordinate (coarseLift current) current time +
            ∑ patch : Fin 4, prepared.rawSourceShapeBudget time current patch ≤ coarsePrecision := by
  classical
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, stageThreshold, stageThresholdPositive, stageEighth,
    compatible, stageCap, stageCapPositive, stageFactors⟩ :=
    exists_uniform_actual_terminal_first_separation orbit normalized sectionTime initialError modelDerivative sectionPositive
      errorPositive errorSmall radiusLarge separationClose outgoing transverse earlierMargin separationAccuracyPositive numericBudget
  obtain ⟨slowCap, slowCapPositive, slowFactors⟩ := exists_uniform_actual_compact_slow_source_profile
  let thresholdMax := stageThreshold
  let rawCap := min stageCap slowCap
  have capStage : rawCap ≤ stageCap := min_le_left _ _
  have capSlow : rawCap ≤ slowCap := min_le_right _ _
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, stageThresholdPositive, stageEighth,
    compatible, rawCap, lt_min stageCapPositive slowCapPositive, ?_⟩
  intro factor factorPositive factorSmall referenceSeparated
  obtain ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRadius, targetRadiusPositive,
    targetRadiusQuarter, rootMin, rootEight, radius, radiusPositive, radiusQuarter,
    passageExtent, passageFour, endpointMax, endpointMaxPositive, endpointMaxOne, parameters⟩ :=
    stageFactors factorPositive factorSmall referenceSeparated
  let accuracy := 1 / (64 * (1 + profileConstant))
  let profileMagnitude := 1 + 16 * (leadingMagnitude + accuracy * profileConstant * costMagnitude +
    (accuracy / 3) * additiveMagnitude)
  let incomingMagnitude := fullProfileConstant * (2 * profileMagnitude + sourceMagnitude)
  have incomingNonnegative : 0 ≤ incomingMagnitude := by
    have one : 1 ≤ profileMagnitude := profileMagnitudeOne
    dsimp only [incomingMagnitude]
    positivity
  refine ⟨incomingMagnitude, incomingNonnegative, rootMin, rootEight, passageExtent, passageFour,
    endpointMax, endpointMaxPositive, endpointMaxOne, ?_⟩
  intro endpoint endpointPositive endpointBound
  filter_upwards [parameters endpoint endpointPositive endpointBound] with incomingTime stageAt
  obtain ⟨sectionAfter, targetPositive, targetSmall, matchingTolerance, matchingTolerancePositive, stageParameters⟩ := stageAt
  let span := sectionTime + 1 - incomingTime
  have spanPositive : 0 < span := by dsimp only [span]; linarith only [sectionAfter]
  obtain ⟨historyMagnitude, historyNonnegative, slowScales⟩ :=
    slowFactors factor factorPositive factorSmall passageExtent ((by norm_num : (1 : ℝ) ≤ 4).trans passageFour)
      span spanPositive.le coefficient coefficientPositive coefficientSmall incomingMagnitude incomingNonnegative
  refine ⟨sectionAfter, targetPositive, targetSmall, matchingTolerance, matchingTolerancePositive,
    historyMagnitude, historyNonnegative, ?_⟩
  intro requestedMatchingAccuracy requestedMatchingAccuracyPositive coarsePrecision coarsePrecisionPositive
  obtain ⟨stageRatio, stageRatioTwo, stageScales⟩ :=
    stageParameters requestedMatchingAccuracy requestedMatchingAccuracyPositive coarsePrecision coarsePrecisionPositive
  refine ⟨max stageRatio 16, stageRatioTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound boundaryConstant boundaryOne ratioSeparation
  have stageRatioLarge : stageRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioSixteen : 16 ≤ scales.ratio := (le_max_right _ _).trans ratioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans stageEighth
  filter_upwards [stageScales scales scaleRoot rootLarge amplitudeIdentity stageRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound boundaryConstant boundaryOne ratioSeparation,
    slowScales scales amplitudePositive ratioSixteen alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    eventually_gt_atTop (0 : ℝ)] with frequency stage slowEstimate frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index source adjacent terminal prescribed
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let growth := 2 * Real.sqrt 2 * omega
  let finish := Real.log (endpoint / changed.seed (index.val + 1)) / growth
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioSixteen]
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
  have payload := stage count phase dipoleAngle (prepared.enlargeCap capStage) path index source adjacent terminal prescribed
  dsimp only at payload
  simp only [rawInvariant, centeredInvariant, sizeInvariant] at payload
  obtain ⟨finishPositive, finishQuarter, elapsed, exposure, finishAvailable, unstableLower, hitData,
    coarserPhysical, targetData, coarseLift, coarseLiftProperties, coarseLiftPolar, coarseFull⟩ := payload
  obtain ⟨hit, hitPositive, hitBefore, hitIdentity, strictBefore, rotation, canonical, rotationNorm, matchingClose, stageData⟩ := hitData
  obtain ⟨compactAvailable, directionNorm, contact, contactInside, firstSeparation, earlier, timing, distance,
    firstSeparationClose, secondSeparationClose, projection, centerUpper, domainBounds⟩ := stageData
  obtain ⟨targetRadial, targetPhysical, lift, liftProperties, liftPolar, _, _, _, _, _, _, _, targetBounds⟩ := targetData
  have hitInside : hit ∈ Icc 0 path.stop := ⟨hitPositive.le, hitBefore.trans finishAvailable⟩
  have weakQuarter (current : Fin count) (before : current.val ≤ index.val) (time : ℝ) (inside : time ∈ Icc 0 hit) :
      |unstableShape motion time current| + |stableShape motion time current| ≤ 1 / 4 := by
    have subset : time ∈ Icc 0 finish := ⟨inside.1, inside.2.trans hitBefore⟩
    rcases lt_or_eq_of_le before with earlier | equal
    · exact ((coarserPhysical time subset current earlier).1.le).trans (by linarith only [radiusQuarter])
    · have same : current = index := Fin.ext equal
      subst current
      exact (targetPhysical time subset).le.trans (by linarith only [targetRadiusQuarter])
  have hitContact : hit ≤ contact := by
    have elapsedNonnegative : 0 ≤ (sectionTime - incomingTime - 1) / omega :=
      div_nonneg (by linarith only [sectionAfter]) omegaPositive.le
    exact (le_add_of_nonneg_right elapsedNonnegative).trans contactInside.1
  have contactAvailable : contact ≤ path.stop := contactInside.2.trans compactAvailable
  have compactSpan : omega * (contact - hit) ≤ span := by
    have upper : contact ≤ hit + span / omega := contactInside.2
    have scaled := mul_le_mul_of_nonneg_left (sub_le_sub_right upper hit) omegaPositive.le
    have identity : omega * (hit + span / omega - hit) = span := by field_simp; ring
    rw [identity] at scaled
    exact scaled
  have incomingProfile (time : ℝ) (inside : time ∈ Icc 0 hit) :
      prepared.rawSourceCenteredState time index + ‖relativeNormalizedFirstMoment changed motion prepared.reference index time‖ +
        ‖quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index‖ / changed.location (index.val + 1) +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
        incomingMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - 0)) :=
    (targetBounds time ⟨inside.1, inside.2.trans hitBefore⟩).2
  have exposureHit : changed.seed (index.val + 1) * Real.exp (growth * (hit - 0)) ≤ 1 := by
    have exponent : growth * (hit - 0) ≤ growth * finish := by
      simpa only [sub_zero] using mul_le_mul_of_nonneg_left hitBefore growthPositive.le
    have bounded := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponent)
      (changed.seed_pos frequencyPositive ratioPositive (index.val + 1)).le
    exact bounded.trans (by rw [exposure]; exact endpointBound.trans endpointMaxOne)
  have slow := slowEstimate count phase dipoleAngle (prepared.enlargeCap capSlow) path index hit hitInside contact
    ⟨hitContact, contactAvailable⟩ compactSpan
    (by
      intro time inside patch
      exact (domainBounds time ⟨hitPositive.le.trans inside.1, inside.2⟩ patch).1)
    (by
      intro time inside patch
      have bound := (domainBounds time ⟨hitPositive.le.trans inside.1, inside.2⟩ patch).2.1
      change ‖patchCentroid prepared.reference time index patch - quadrupoleCenter prepared.reference time index‖ ≤
        passageExtent * changed.length (index.val + 1)
      rw [prepared.referenceIdentity]
      exact bound)
    0 (by intro time inside; simpa only [rawInvariant, centeredInvariant] using incomingProfile time inside) exposureHit
  dsimp only at slow
  simp only [rawInvariant, centeredInvariant] at slow
  refine ⟨finishPositive, finishQuarter, elapsed, exposure, finishAvailable, unstableLower, ?_, ?_,
    coarseLift, coarseLiftProperties, coarseLiftPolar, coarseFull⟩
  · refine ⟨hit, hitPositive, hitBefore, hitIdentity, strictBefore, weakQuarter, ?_, ?_,
      rotation, canonical, rotationNorm, matchingClose, compactAvailable, directionNorm, contact, contactInside,
      ⟨hitContact, contactAvailable⟩, firstSeparation, earlier, timing, distance,
      firstSeparationClose, secondSeparationClose, projection, centerUpper, slow, domainBounds⟩
    · intro time inside
      simpa only [sub_zero] using incomingProfile time inside
    · simpa only [sub_zero] using exposureHit
  · refine ⟨lift, liftProperties, liftPolar, ?_⟩
    intro time inside
    simpa only [sub_zero] using (targetBounds time inside).1

end EulerNonuniqueness.Paper
