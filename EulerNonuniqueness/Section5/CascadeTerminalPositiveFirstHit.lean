import EulerNonuniqueness.Section5.CascadeTerminalAvailableIncoming
import EulerNonuniqueness.Section5.CascadeTerminalFinerInitialData
import EulerNonuniqueness.Section6.SourcePacketTerminalPositiveWindowOfSection
import EulerNonuniqueness.Section5.CascadeGivenMapIncomingWeightedErrors
import EulerNonuniqueness.Section5.CascadeTerminalDuhamelLowerBound
import EulerNonuniqueness.Section5.CascadeUnstableFirstHit

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_terminal_positive_first_hit (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) (sectionTime initialError : ℝ)
    (sectionPositive : 0 < sectionTime)
    (errorNonnegative : 0 ≤ initialError) (errorSmall : initialError ≤ 1 / 64)
    (radiusLarge : 2048 ≤ separationRadius orbit sectionTime)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ initialError / 2)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re)
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
      ∃ stableConstant ≥ (1 : ℝ), ∃ profileConstant ≥ (1 : ℝ),
      ∃ costMagnitude ≥ (1 : ℝ), ∃ leadingMagnitude ≥ (1 : ℝ), ∃ additiveMagnitude ≥ (0 : ℝ),
      let accuracy := 1 / (64 * (1 + profileConstant))
      let profileMagnitude := 1 + 16 * (leadingMagnitude + accuracy * profileConstant * costMagnitude +
        (accuracy / 3) * additiveMagnitude)
      1 ≤ profileMagnitude ∧
      ∃ fullProfileConstant ≥ (1 : ℝ), ∃ sourceMagnitude ≥ (1 : ℝ),
      ∃ targetRadius > (0 : ℝ), targetRadius ≤ 1 / 4 ∧
      ∃ rootMin ≥ (8 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ endpointMax > (0 : ℝ),
      endpointMax ≤ 1 ∧ ∀ endpoint : ℝ, 0 < endpoint → endpoint ≤ endpointMax →
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
      (∀ level : ℝ, 0 < level → level ≤ endpoint / 2 →
        ∃ hit : ℝ, 0 < hit ∧ hit ≤ finish ∧
          (referenceStraightenedShape motion graph coordinate index hit -
            referenceStraightenedShape prepared.reference graph coordinate index hit).1 = level ∧
          ∀ time : ℝ, 0 ≤ time → time < hit →
            (referenceStraightenedShape motion graph coordinate index time -
              referenceStraightenedShape prepared.reference graph coordinate index time).1 < level) ∧
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
    coordinateDerivative, chartConstant, chartOne, incomingThreshold, incomingThresholdPositive, incomingEighth,
    compatible, incomingCap, incomingCapPositive, incomingFactors⟩ :=
    exists_uniform_actual_terminal_available_incoming orbit normalized sectionTime initialError sectionPositive
      errorNonnegative errorSmall radiusLarge separationClose outgoing
  obtain ⟨errorThreshold, errorThresholdPositive, errorEighth, errorCap, errorCapPositive, errorFactors⟩ :=
    exists_uniform_actual_given_map_incoming_weighted_errors graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨_, _, windowThreshold, windowThresholdPositive, windowEighth, windows⟩ :=
    exists_actual_terminal_positive_window_of_section orbit sectionTime initialError errorNonnegative errorSmall
      radiusLarge separationClose outgoing
  obtain ⟨windowRatio, windowRatioTwo, windowScales⟩ := windows (1 / 8) (by norm_num) le_rfl numericBudget
  obtain ⟨duhamelRadius, duhamelPositive, _, duhamel⟩ :=
    exists_uniform_actual_terminal_duhamel_lower_bound graphAnalytic.contDiffAt coordinateSmooth
  obtain ⟨hitRadius, hitPositive, _, firstHit⟩ :=
    exists_uniform_actual_unstable_first_hit graphAnalytic.contDiffAt coordinateSmooth
  let physicalRadius := min duhamelRadius hitRadius
  have physicalPositive : 0 < physicalRadius := lt_min duhamelPositive hitPositive
  obtain ⟨physicalPrecision, physicalPrecisionPositive, refinePhysical⟩ :=
    exists_uniform_actual_full_state_physical_refinement graphAnalytic.contDiffAt coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative physicalPositive
  let thresholdMax := min incomingThreshold (min errorThreshold windowThreshold)
  let rawCap := min incomingCap errorCap
  have thresholdPositive : 0 < thresholdMax := lt_min incomingThresholdPositive (lt_min errorThresholdPositive windowThresholdPositive)
  have thresholdIncoming : thresholdMax ≤ incomingThreshold := min_le_left _ _
  have thresholdErrors : thresholdMax ≤ errorThreshold := (min_le_right _ _).trans (min_le_left _ _)
  have thresholdWindow : thresholdMax ≤ windowThreshold := (min_le_right _ _).trans (min_le_right _ _)
  have capIncoming : rawCap ≤ incomingCap := min_le_left _ _
  have capErrors : rawCap ≤ errorCap := min_le_right _ _
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive,
    thresholdIncoming.trans incomingEighth, compatible, rawCap, lt_min incomingCapPositive errorCapPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRadius, targetRadiusPositive,
    targetRadiusQuarter, incomingRoot, incomingRootEight, radius, radiusPositive, radiusQuarter,
    incomingEndpoint, incomingEndpointPositive, incomingEndpointOne, incomingParameters⟩ :=
    incomingFactors factorPositive factorSmall
  let accuracy := 1 / (64 * (1 + profileConstant))
  let profileMagnitude := 1 + 16 * (leadingMagnitude + accuracy * profileConstant * costMagnitude +
    (accuracy / 3) * additiveMagnitude)
  let currentMagnitude := fullProfileConstant * (2 * profileMagnitude + sourceMagnitude)
  have currentNonnegative : 0 ≤ currentMagnitude := by
    have one : 1 ≤ profileMagnitude := profileMagnitudeOne
    dsimp only [currentMagnitude]
    positivity
  obtain ⟨errorRoot, errorRootEight, errorMagnitudes⟩ := errorFactors factor factorPositive factorSmall
  obtain ⟨coarsePrecision, coarsePrecisionPositive, errorEndpoint, errorEndpointPositive, _, errorParameters⟩ :=
    errorMagnitudes currentMagnitude currentMagnitude currentNonnegative currentNonnegative
  let rootMin := max incomingRoot errorRoot
  let endpointMax := min incomingEndpoint (min errorEndpoint (physicalPrecision / (currentMagnitude + 1)))
  have endpointMaxPositive : 0 < endpointMax := by dsimp only [endpointMax]; positivity
  have endpointMaxIncoming : endpointMax ≤ incomingEndpoint := min_le_left _ _
  have endpointMaxErrors : endpointMax ≤ errorEndpoint := (min_le_right _ _).trans (min_le_left _ _)
  have endpointMaxPhysical : endpointMax ≤ physicalPrecision / (currentMagnitude + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRadius, targetRadiusPositive,
    targetRadiusQuarter, rootMin, incomingRootEight.trans (le_max_left _ _), radius, radiusPositive, radiusQuarter,
    endpointMax, endpointMaxPositive, endpointMaxIncoming.trans incomingEndpointOne, ?_⟩
  intro endpoint endpointPositive endpointBound precision precisionPositive
  let selectedPrecision := min precision coarsePrecision
  have selectedPositive : 0 < selectedPrecision := lt_min precisionPositive coarsePrecisionPositive
  obtain ⟨incomingRatio, incomingRatioTwo, incomingScales⟩ :=
    incomingParameters endpoint endpointPositive (endpointBound.trans endpointMaxIncoming) selectedPrecision selectedPositive
  let modelBound := max 3 (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)
  let extent := max 4 (modelBound + 1)
  let magnitude := modelBound + 2
  have boundThree : 3 ≤ modelBound := le_max_left _ _
  have extentOne : 1 ≤ extent := (by norm_num : (1 : ℝ) ≤ 4).trans (le_max_left _ _)
  have magnitudeNonnegative : 0 ≤ magnitude := by dsimp only [magnitude]; linarith only [boundThree]
  obtain ⟨errorRatio, _, errorScales⟩ := errorParameters extent magnitude (separationRadius orbit sectionTime) (1 / 16)
    extentOne magnitudeNonnegative (by linarith only [radiusLarge]) (by norm_num)
  let ratioMin := max incomingRatio (max errorRatio (max windowRatio 128))
  refine ⟨ratioMin, incomingRatioTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound boundaryConstant boundaryOne ratioSeparation
  have incomingRatioLarge : incomingRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have errorRatioLarge : errorRatio ≤ scales.ratio := (le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge)
  have windowRatioLarge : windowRatio ≤ scales.ratio := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge))
  have ratio128 : 128 ≤ scales.ratio := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge))
  have ratioBound : 2 ≤ scales.ratio := incomingRatioTwo.trans incomingRatioLarge
  have incomingRootLarge : incomingRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have errorRootLarge : errorRoot ≤ scaleRoot := (le_max_right _ _).trans rootLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (incomingRootEight.trans incomingRootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := (thresholdBound.trans thresholdIncoming).trans incomingEighth
  filter_upwards [incomingScales scales scaleRoot incomingRootLarge amplitudeIdentity incomingRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdIncoming)
      boundaryConstant boundaryOne ratioSeparation,
    errorScales scales scaleRoot errorRootLarge amplitudeIdentity errorRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdErrors)
      orbit sectionTime boundaryConstant 0 boundaryOne le_rfl ratioSeparation,
    eventually_actual_terminal_finer_initial_data orbit sectionTime initialError errorNonnegative errorSmall radiusLarge
      separationClose outgoing scales amplitudePositive ratio128 alphaPositive,
    windowScales scales amplitudePositive alphaPositive windowRatioLarge referenceConstant referenceNonnegative referenceAmplitude
      threshold (thresholdBound.trans thresholdWindow) factor scaleRoot boundaryConstant factorPositive
      (factorSmall.trans (by norm_num)) rootOne boundaryOne,
    duhamel scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne
      factorPositive (factorSmall.trans (by norm_num)),
    refinePhysical scales ratioBound alphaPositive referenceConstant referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative
      (by positivity : 0 < physicalRadius / 8), eventually_gt_atTop (0 : ℝ)]
    with frequency incoming errors finerData window lowerBound physical referenceSmall frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index source adjacent terminal prescribed
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  let finish := Real.log (endpoint / changed.seed (index.val + 1)) / growth
  have nonterminal : index.val + 1 < count := by omega
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time current patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  have sizeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateSize graph coordinate = prepared.finiteCoordinateSize graph coordinate := rfl
  have payload := incoming count phase dipoleAngle (prepared.enlargeCap capIncoming) path index source adjacent terminal prescribed
  dsimp only at payload
  simp only [rawInvariant, centeredInvariant, sizeInvariant] at payload
  obtain ⟨finishPositive, finishQuarter, elapsed, exposure, finishAvailable, coarserPhysical, targetData,
    coarseLift, coarseLiftProperties, coarseLiftPolar, coarseFull⟩ := payload
  have savedTarget := targetData
  obtain ⟨targetRadial, targetPhysical, lift, liftProperties, liftPolar,
    shapeContinuous, shapeZero, shapeProfile, stateContinuous, stateZero, stateI, forcingI, targetBounds⟩ := targetData
  have finishInside : finish ∈ Icc 0 path.stop := ⟨finishPositive.le, finishAvailable⟩
  have weakPhysical (current : Fin count) (before : current.val ≤ index.val) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape motion time current| + |stableShape motion time current| ≤ 1 / 4 := by
    rcases lt_or_eq_of_le before with earlier | equal
    · exact ((coarserPhysical time inside current earlier).1.le).trans (by linarith only [radiusQuarter])
    · have same : current = index := Fin.ext equal
      subst current
      exact (targetPhysical time inside).le.trans (by linarith only [targetRadiusQuarter])
  have currentProfile (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.finiteCoordinateSize graph coordinate lift index time + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
        currentMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - 0)) :=
    (targetBounds time inside).1
  have sharpProfile (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.rawSourceCenteredState time index + ‖relativeNormalizedFirstMoment changed motion prepared.reference index time‖ +
        ‖quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index‖ / changed.location (index.val + 1) +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
        currentMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - 0)) :=
    (targetBounds time inside).2
  obtain ⟨_, finerEq, entries, extents, sourceProfiles, domains, rateGaps, nearestTiming, sourceTiming⟩ :=
    finerData count phase dipoleAngle prepared path (thresholdSmall.trans (by norm_num)) index source adjacent terminal
  let direction := Complex.exp (Complex.I * (dipoleAngle count : ℂ))
  have weighted := errors count phase dipoleAngle (prepared.enlargeCap capErrors) path index nonterminal
    (fun _ => 0) (fun _ => separationRadius orbit sectionTime) (fun _ => direction)
    entries extents (fun _ => magnitude) (by
      intro current finer
      refine ⟨magnitudeNonnegative, ?_⟩
      intro time inside
      simpa only [rawInvariant, centeredInvariant] using sourceProfiles current finer time inside)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) domains (fun _ => 0) (fun _ => rfl) nearestTiming sourceTiming
    (fun _ _ => le_rfl) finish finishInside weakPhysical lift
    (fun side => (liftProperties side).1.continuousOn) (fun side => (liftProperties side).2) liftPolar rateGaps
    (by intro time inside; simpa only [rawInvariant, sizeInvariant] using currentProfile time inside)
    (by intro time inside; simpa only [rawInvariant, centeredInvariant] using sharpProfile time inside)
    coarseLift (by
      intro current earlier time inside
      simpa only [rawInvariant, sizeInvariant] using
        (coarseFull time inside current earlier).trans (min_le_right precision coarsePrecision))
    (by simpa only [sub_zero] using exposure.le.trans (endpointBound.trans endpointMaxErrors))
  dsimp only at weighted
  have remainderSmall := weighted.2.2.1
  have coarseSmall := weighted.2.2.2.2.2.2
  simp only [mul_zero, Real.exp_zero, one_mul] at remainderSmall coarseSmall
  have fullSmall (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.finiteCoordinateSize graph coordinate lift index time + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
        physicalPrecision := by
    have growthPositive : 0 < growth := by
      have omegaPositive := changed.omega_pos frequencyPositive
        (by change 0 < scales.ratio; linarith only [ratioBound]) (index.val + 1)
      dsimp only [growth]
      positivity
    have qBound : changed.seed (index.val + 1) * Real.exp (growth * (time - 0)) ≤ endpoint := by
      rw [← exposure]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (by simpa only [sub_zero] using inside.2) growthPositive.le))
        (changed.seed_pos frequencyPositive (by change 0 < scales.ratio; linarith only [ratioBound]) _).le
    have scaled := mul_le_mul_of_nonneg_left (endpointBound.trans endpointMaxPhysical)
      (show 0 ≤ currentMagnitude + 1 by positivity)
    have identity : (currentMagnitude + 1) * (physicalPrecision / (currentMagnitude + 1)) = physicalPrecision := by
      field_simp
    rw [identity] at scaled
    have magnitudeBound : currentMagnitude * endpoint ≤ physicalPrecision := by
      nlinarith only [scaled, endpointPositive]
    calc
      _ ≤ currentMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - 0)) := currentProfile time inside
      _ = currentMagnitude * (changed.seed (index.val + 1) * Real.exp (growth * (time - 0))) := by ring
      _ ≤ currentMagnitude * endpoint := mul_le_mul_of_nonneg_left qBound currentNonnegative
      _ ≤ physicalPrecision := magnitudeBound
  have refined := physical prepared path factorPositive index nonterminal finish finishInside
    (fun time inside => weakPhysical index le_rfl time inside) lift fullSmall
  have pairedPhysical (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| < physicalRadius := by
    fin_cases side
    · exact refined time inside
    · have reference := referenceSmall prepared.toCascadeMaterialPreparedPair time
        ⟨inside.1, inside.2.trans (finishAvailable.trans path.stopBound)⟩ index
      have unused := abs_nonneg (diagonalDifference prepared.reference time index / changed.length (index.val + 1) ^ 2 - 1)
      change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < physicalRadius
      linarith only [reference, unused, physicalPositive]
  obtain ⟨_, _, _, nearestEstimates⟩ := window count phase dipoleAngle prepared.toCascadeMaterialPreparedPair prescribed
    path index source adjacent terminal
  have nearestLower := (nearestEstimates finish finishPositive.le finishAvailable elapsed).2
  have seedPositive : 0 < changed.seed (index.val + 1) :=
    changed.seed_pos frequencyPositive (by change 0 < scales.ratio; linarith only [ratioBound]) _
  have nearestBound : 3 * changed.seed (index.val + 1) / 4 ≤ ∫ time in (0 : ℝ)..finish,
      Real.exp (-growth * time) * (relativeBlockSourceShapeInput changed motion prepared.reference index source time).1 := by
    have scaled := (le_div_iff₀ seedPositive).mp nearestLower
    linarith only [scaled]
  have actualLower := lowerBound count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index source adjacent terminal
    finish finishPositive.le finishAvailable
    (fun side time inside => (pairedPhysical side time inside).trans_le (min_le_left _ _))
    nearestBound (by simpa only [mul_comm, div_eq_mul_inv, one_mul] using coarseSmall)
    (by simpa only [mul_comm, div_eq_mul_inv, one_mul] using remainderSmall)
  have unstableLower : endpoint / 2 ≤ (referenceStraightenedShape motion graph coordinate index finish -
      referenceStraightenedShape prepared.reference graph coordinate index finish).1 := by
    rw [exposure] at actualLower
    exact actualLower
  have hits (level : ℝ) (levelPositive : 0 < level) (levelBound : level ≤ endpoint / 2) :=
    firstHit prepared.toCascadeMaterialPreparedPair path index nonterminal finish finishPositive.le finishAvailable
      (fun side time inside => (pairedPhysical side time inside).trans_le (min_le_right _ _))
      level levelPositive (levelBound.trans unstableLower)
  refine ⟨finishPositive, finishQuarter, elapsed, exposure, finishAvailable, unstableLower, hits,
    coarserPhysical, savedTarget, coarseLift, coarseLiftProperties, coarseLiftPolar, ?_⟩
  intro time inside current earlier
  exact (coarseFull time inside current earlier).trans (min_le_left precision coarsePrecision)

end EulerNonuniqueness.Paper
