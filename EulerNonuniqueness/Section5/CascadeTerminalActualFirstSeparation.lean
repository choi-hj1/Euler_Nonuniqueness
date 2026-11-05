import EulerNonuniqueness.Section5.CascadeTerminalMatchedFirstHit
import EulerNonuniqueness.Section5.CascadeJointPostHitFollowerBootstrap
import EulerNonuniqueness.Section5.CascadeMatchedFirstSeparationStage

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_terminal_first_separation (orbit : SeparatingOrbit)
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
      ∃ stableConstant ≥ (1 : ℝ), ∃ profileConstant ≥ (1 : ℝ),
      ∃ costMagnitude ≥ (1 : ℝ), ∃ leadingMagnitude ≥ (1 : ℝ), ∃ additiveMagnitude ≥ (0 : ℝ),
      let accuracy := 1 / (64 * (1 + profileConstant))
      let profileMagnitude := 1 + 16 * (leadingMagnitude + accuracy * profileConstant * costMagnitude +
        (accuracy / 3) * additiveMagnitude)
      1 ≤ profileMagnitude ∧
      ∃ fullProfileConstant ≥ (1 : ℝ), ∃ sourceMagnitude ≥ (1 : ℝ),
      ∃ targetRadius > (0 : ℝ), targetRadius ≤ 1 / 4 ∧
      ∃ rootMin ≥ (8 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ passageExtent ≥ (4 : ℝ), ∃ endpointMax > (0 : ℝ),
      endpointMax ≤ 1 ∧ ∀ endpoint : ℝ, 0 < endpoint → endpoint ≤ endpointMax →
      ∀ᶠ incomingTime : ℝ in atBot,
      incomingTime + 1 < sectionTime ∧ 0 < coordinate (orbitUnstableShape orbit incomingTime) ∧
      coordinate (orbitUnstableShape orbit incomingTime) ≤ endpoint / 2 ∧
      ∃ matchingTolerance > (0 : ℝ),
      ∀ requestedMatchingAccuracy > (0 : ℝ),
      ∀ precision : ℝ, 0 < precision →
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
      let shape := fun time =>
        |(referenceStraightenedShape motion graph coordinate index time).1 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
        |(referenceStraightenedShape motion graph coordinate index time).2 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).2|
      let origin := (0 : ℝ)
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
            ∀ time ∈ Icc 0 contact, ∀ patch : Fin 4,
              ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤ passageExtent * length ∧
              ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index patch -
                quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index‖ ≤ passageExtent * length ∧
              motion.domain time index patch ⊆ Metric.closedBall (quadrupoleCenter motion time index) (passageExtent * length) ∧
              prepared.referenceWitness.trajectory.movingFamily.patchMotion.domain time index patch ⊆
                Metric.closedBall (quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index)
                  (passageExtent * length)) ∧
      (∀ time ∈ Icc 0 finish, ∀ receiver : Fin count, receiver.val < index.val →
        (|unstableShape motion time receiver| + |stableShape motion time receiver| < radius / 2) ∧
        |radialShape motion time receiver| < 1 / 8) ∧
      ((∀ time ∈ Icc 0 finish, |radialShape motion time index| < 1 / 2) ∧
      (∀ time ∈ Icc 0 finish, |unstableShape motion time index| + |stableShape motion time index| < targetRadius / 2) ∧
      ∃ lift : Fin 2 → ℝ → ℝ,
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
      ContinuousOn shape (Icc 0 finish) ∧ shape 0 = 0 ∧
      (∀ time ∈ Icc 0 finish,
        shape time < profileMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) ∧
        shape time ≤ (profileMagnitude / 2) * changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) ∧
      ContinuousOn state (Icc 0 finish) ∧ state 0 = 0 ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * state time) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * forcing time) volume 0 finish ∧
      ∀ time ∈ Icc 0 finish,
        state time ≤ fullProfileConstant * (2 * profileMagnitude + sourceMagnitude) *
          changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) ∧
        sharp time ≤ fullProfileConstant * (2 * profileMagnitude + sourceMagnitude) *
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
    coordinateDerivative, chartConstant, chartOne, matchThreshold, matchThresholdPositive, matchEighth,
    compatible, matchCap, matchCapPositive, matchFactors⟩ :=
    exists_uniform_actual_terminal_matched_first_hit orbit normalized sectionTime initialError sectionPositive
      errorPositive.le errorSmall radiusLarge separationClose outgoing numericBudget
  obtain ⟨postThreshold, postThresholdPositive, _, postCap, postCapPositive, postFactors⟩ :=
    exists_uniform_actual_joint_post_hit_follower_bootstrap graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  let thresholdMax := min matchThreshold postThreshold
  let rawCap := min matchCap postCap
  have thresholdMatch : thresholdMax ≤ matchThreshold := min_le_left _ _
  have thresholdPost : thresholdMax ≤ postThreshold := min_le_right _ _
  have capMatch : rawCap ≤ matchCap := min_le_left _ _
  have capPost : rawCap ≤ postCap := min_le_right _ _
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, lt_min matchThresholdPositive postThresholdPositive,
    thresholdMatch.trans matchEighth, compatible, rawCap, lt_min matchCapPositive postCapPositive, ?_⟩
  intro factor factorPositive factorSmall referenceSeparated
  obtain ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRadius, targetRadiusPositive,
    targetRadiusQuarter, matchRoot, matchRootEight, radius, radiusPositive, radiusQuarter,
    endpointMax, endpointMaxPositive, endpointMaxOne, matchParameters⟩ := matchFactors factorPositive factorSmall
  obtain ⟨_, _, _, postRoot, _, postParameters⟩ := postFactors factor factorPositive factorSmall
  obtain ⟨passageExtent, passageFour, passageParameters⟩ := exists_uniform_actual_matched_first_separation_stage orbit normalized
    sectionTime modelDerivative ((by norm_num : (512 : ℝ) ≤ 2048).trans radiusLarge) transverse earlierMargin
    factorPositive (factorSmall.trans (by norm_num)) separationAccuracyPositive errorPositive errorSmall
    referenceSeparated separationClose outgoing
  let rootMin := max matchRoot postRoot
  let accuracy := 1 / (64 * (1 + profileConstant))
  let profileMagnitude := 1 + 16 * (leadingMagnitude + accuracy * profileConstant * costMagnitude +
    (accuracy / 3) * additiveMagnitude)
  let currentMagnitude := fullProfileConstant * (2 * profileMagnitude + sourceMagnitude)
  have currentNonnegative : 0 ≤ currentMagnitude := by
    have one : 1 ≤ profileMagnitude := profileMagnitudeOne
    dsimp only [currentMagnitude]
    positivity
  refine ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRadius, targetRadiusPositive,
    targetRadiusQuarter, rootMin, matchRootEight.trans (le_max_left _ _), radius, radiusPositive, radiusQuarter,
    passageExtent, passageFour, endpointMax, endpointMaxPositive, endpointMaxOne, ?_⟩
  intro endpoint endpointPositive endpointBound
  filter_upwards [matchParameters endpoint endpointPositive endpointBound, eventually_lt_atBot (sectionTime - 1)]
    with incomingTime incoming incomingEarlier
  obtain ⟨_, targetPositive, targetSmall, matchAt⟩ := incoming
  have sectionAfter : incomingTime + 1 < sectionTime := by linarith only [incomingEarlier]
  obtain ⟨matchingTolerance, matchingTolerancePositive, passageScales⟩ := passageParameters incomingTime sectionAfter
  refine ⟨sectionAfter, targetPositive, targetSmall, matchingTolerance, matchingTolerancePositive, ?_⟩
  intro requestedMatchingAccuracy requestedMatchingAccuracyPositive precision precisionPositive
  obtain ⟨matchRatio, matchRatioTwo, matchScales⟩ :=
    matchAt (min (matchingTolerance / 2) requestedMatchingAccuracy)
      (lt_min (half_pos matchingTolerancePositive) requestedMatchingAccuracyPositive) precision precisionPositive
  let span := sectionTime + 1 - incomingTime
  have spanPositive : 0 < span := by dsimp only [span]; linarith only [sectionAfter]
  let modelBound := max 3 (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)
  let extent := max 4 (modelBound + 1)
  let magnitude := modelBound + 2
  have boundThree : 3 ≤ modelBound := le_max_left _ _
  have extentOne : 1 ≤ extent := (by norm_num : (1 : ℝ) ≤ 4).trans (le_max_left _ _)
  have magnitudeNonnegative : 0 ≤ magnitude := by dsimp only [magnitude]; linarith only [boundThree]
  obtain ⟨postRatio, _, postScales⟩ := postParameters precision precisionPositive span spanPositive.le currentMagnitude currentNonnegative
    extent magnitude (separationRadius orbit sectionTime) (1 / 16) extentOne magnitudeNonnegative
    (by linarith only [radiusLarge]) (by norm_num) (by norm_num)
  let ratioMin := max matchRatio (max postRatio 128)
  refine ⟨ratioMin, matchRatioTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound boundaryConstant boundaryOne ratioSeparation
  have matchRatioLarge : matchRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have postRatioLarge : postRatio ≤ scales.ratio := (le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge)
  have ratio128 : 128 ≤ scales.ratio := (le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge)
  have ratioBound : 2 ≤ scales.ratio := matchRatioTwo.trans matchRatioLarge
  have matchRootLarge : matchRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have postRootLarge : postRoot ≤ scaleRoot := (le_max_right _ _).trans rootLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (matchRootEight.trans matchRootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := (thresholdBound.trans thresholdMatch).trans matchEighth
  filter_upwards [matchScales scales scaleRoot matchRootLarge amplitudeIdentity matchRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdMatch)
      boundaryConstant boundaryOne ratioSeparation,
    postScales scales scaleRoot postRootLarge amplitudeIdentity postRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdPost)
      orbit sectionTime boundaryConstant 0 boundaryOne le_rfl ratioSeparation,
    eventually_actual_terminal_finer_initial_data orbit sectionTime initialError errorPositive.le errorSmall radiusLarge separationClose outgoing
      scales amplitudePositive ratio128 alphaPositive,
    passageScales scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative
      (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    eventually_ge_atTop (max 1 (4 * span + 1))]
    with frequency matched post finerData passage frequencyLarge
  intro count phase dipoleAngle shapeRadius monitor prepared path index source adjacent terminal prescribed
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let growth := 2 * Real.sqrt 2 * omega
  let finish := Real.log (endpoint / changed.seed (index.val + 1)) / growth
  have nonterminal : index.val + 1 < count := by omega
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le ((le_max_left _ _).trans frequencyLarge)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaLower : frequency ≤ omega := changed.omega_ge_frequency frequencyPositive
    (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _
  have growthPositive : 0 < growth := by dsimp only [growth]; positivity
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time current patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  have sizeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateSize graph coordinate = prepared.finiteCoordinateSize graph coordinate := rfl
  have payload := matched count phase dipoleAngle (prepared.enlargeCap capMatch) path index source adjacent terminal prescribed
  dsimp only at payload
  simp only [rawInvariant, centeredInvariant, sizeInvariant] at payload
  obtain ⟨finishPositive, finishQuarter, elapsed, exposure, finishAvailable, unstableLower, hitData,
    coarserPhysical, targetData, coarseLift, coarseLiftProperties, coarseLiftPolar, coarseFull⟩ := payload
  obtain ⟨hit, hitPositive, hitBefore, hitIdentity, strictBefore, rotation, canonical, rotationNorm, matchingClose⟩ := hitData
  have savedTarget := targetData
  obtain ⟨targetRadial, targetPhysical, lift, liftProperties, liftPolar,
    shapeContinuous, shapeZero, shapeProfile, stateContinuous, stateZero, stateI, forcingI, targetBounds⟩ := targetData
  have hitInside : hit ∈ Icc 0 path.stop := ⟨hitPositive.le, hitBefore.trans finishAvailable⟩
  let compactEndpoint := hit + span / omega
  let candidate := min path.stop compactEndpoint
  have hitEndpoint : hit ≤ compactEndpoint := le_add_of_nonneg_right (div_nonneg spanPositive.le omegaPositive.le)
  have candidateInside : candidate ∈ Icc 0 path.stop :=
    ⟨le_min path.stopPositive.le (hitPositive.le.trans hitEndpoint), min_le_left _ _⟩
  have compactSmall : compactEndpoint ≤ 1 := by
    have frequencyBound : 4 * span + 1 ≤ frequency := (le_max_right _ _).trans frequencyLarge
    have omegaBound : 4 * span + 1 ≤ omega := frequencyBound.trans omegaLower
    have fraction : span / omega ≤ 1 / 4 := (div_le_iff₀ omegaPositive).mpr (by
      have bound : 4 * span ≤ omega := (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans omegaBound
      calc
        span = (1 / 4 : ℝ) * (4 * span) := by ring
        _ ≤ (1 / 4 : ℝ) * omega := mul_le_mul_of_nonneg_left bound (by norm_num))
    dsimp only [compactEndpoint]
    linarith only [hitBefore, finishQuarter, fraction]
  have shortSpan : omega * (candidate - hit) ≤ span := by
    have scaled := mul_le_mul_of_nonneg_left (sub_le_sub_right (min_le_right path.stop compactEndpoint) hit) omegaPositive.le
    have identity : omega * (compactEndpoint - hit) = span := by
      dsimp only [compactEndpoint]
      field_simp
      ring
    rw [identity] at scaled
    exact scaled
  have exposureHit : changed.seed (index.val + 1) * Real.exp (growth * (hit - 0)) ≤ 1 := by
    have exponent : growth * (hit - 0) ≤ growth * finish := by
      simpa only [sub_zero] using mul_le_mul_of_nonneg_left hitBefore growthPositive.le
    have bounded := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponent)
      (changed.seed_pos frequencyPositive ratioPositive (index.val + 1)).le
    exact bounded.trans (by rw [exposure]; exact endpointBound.trans endpointMaxOne)
  obtain ⟨_, _, entries, extents, sourceProfiles, domains, rateGaps, nearestTiming, sourceTiming⟩ :=
    finerData count phase dipoleAngle prepared path (thresholdSmall.trans (by norm_num)) index source adjacent terminal
  let direction := Complex.exp (Complex.I * (dipoleAngle count : ℂ))
  have followers := post count phase dipoleAngle (prepared.enlargeCap capPost) path index nonterminal
    (fun _ => 0) (fun _ => separationRadius orbit sectionTime) (fun _ => direction)
    entries extents (fun _ => magnitude) (by
      intro current finer
      refine ⟨magnitudeNonnegative, ?_⟩
      intro time inside
      simpa only [rawInvariant, centeredInvariant] using sourceProfiles current finer time inside)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) domains (fun _ => 0) (fun _ => rfl)
    nearestTiming sourceTiming (fun _ _ => le_rfl) candidate candidateInside hit hitInside rateGaps hitPositive.le shortSpan
    (by
      intro time inside
      simpa only [rawInvariant, centeredInvariant] using (targetBounds time ⟨inside.1, inside.2.trans hitBefore⟩).2)
    exposureHit
  obtain ⟨coarseControl, _, _, _, _⟩ := followers
  have stage := passage count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index nonterminal hit hitInside
    (fun time inside => (targetRadial time ⟨inside.1, inside.2.trans hitBefore⟩).le) rotation rotationNorm
    (matchingClose.le.trans ((min_le_left _ _).trans (half_le_self matchingTolerancePositive.le))) compactSmall (by
      intro other different otherNonterminal
      have differentValues : other.val ≠ index.val := by
        intro equal
        exact different (Fin.ext equal)
      have earlier : other.val < index.val := by omega
      left
      intro time inside
      exact ((coarseControl time inside other earlier).2.le).trans (by norm_num))
  refine ⟨finishPositive, finishQuarter, elapsed, exposure, finishAvailable, unstableLower,
    ⟨hit, hitPositive, hitBefore, hitIdentity, strictBefore, rotation, canonical, rotationNorm, ?_, ?_⟩,
    coarserPhysical, savedTarget, coarseLift, coarseLiftProperties, coarseLiftPolar, coarseFull⟩
  · exact matchingClose.trans_le (min_le_min (half_le_self matchingTolerancePositive.le) le_rfl)
  · exact stage

end EulerNonuniqueness.Paper
