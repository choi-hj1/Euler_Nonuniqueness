import EulerNonuniqueness.Section5.CascadeTerminalPositiveFirstHit
import EulerNonuniqueness.Section5.CascadeAccurateStraightenedHitMatch
import EulerNonuniqueness.Section6.NormalizedOrbitDepartureTarget

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_terminal_matched_first_hit (orbit : SeparatingOrbit)
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
      ∀ᶠ incomingTime : ℝ in atBot,
      incomingTime < sectionTime ∧ 0 < coordinate (orbitUnstableShape orbit incomingTime) ∧
      coordinate (orbitUnstableShape orbit incomingTime) ≤ endpoint / 2 ∧
      ∀ matchingAccuracy : ℝ, 0 < matchingAccuracy →
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
            centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ < matchingAccuracy) ∧
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
    coordinateDerivative, chartConstant, chartOne, firstThreshold, firstThresholdPositive, firstEighth,
    compatible, firstCap, firstCapPositive, firstFactors⟩ :=
    exists_uniform_actual_terminal_positive_first_hit orbit normalized sectionTime initialError sectionPositive
      errorNonnegative errorSmall radiusLarge separationClose outgoing numericBudget
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
  obtain ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRadius, targetRadiusPositive,
    targetRadiusQuarter, firstRoot, firstRootEight, radius, radiusPositive, radiusQuarter,
    firstEndpoint, firstEndpointPositive, firstEndpointOne, firstParameters⟩ :=
    firstFactors factorPositive factorSmall
  let accuracy := 1 / (64 * (1 + profileConstant))
  let profileMagnitude := 1 + 16 * (leadingMagnitude + accuracy * profileConstant * costMagnitude +
    (accuracy / 3) * additiveMagnitude)
  let currentMagnitude := fullProfileConstant * (2 * profileMagnitude + sourceMagnitude)
  have currentNonnegative : 0 ≤ currentMagnitude := by
    have one : 1 ≤ profileMagnitude := profileMagnitudeOne
    dsimp only [currentMagnitude]
    positivity
  obtain ⟨matchRadius, matchRadiusPositive, _, matchRoot, _, matchMagnitudes⟩ :=
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
  refine ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRadius, targetRadiusPositive,
    targetRadiusQuarter, rootMin, firstRootEight.trans (le_max_left _ _), radius, radiusPositive, radiusQuarter,
    endpointMax, endpointMaxPositive, endpointMaxFirst.trans firstEndpointOne, ?_⟩
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
  intro matchingAccuracy matchingAccuracyPositive precision precisionPositive
  let selectedPrecision := min precision physicalPrecision
  have selectedPositive : 0 < selectedPrecision := lt_min precisionPositive physicalPrecisionPositive
  obtain ⟨firstRatio, firstRatioTwo, firstScales⟩ :=
    firstParameters endpoint endpointPositive (endpointBound.trans endpointMaxFirst) selectedPrecision selectedPositive
  let modelBound := max 3 (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)
  let extent := max 4 (modelBound + 1)
  let magnitude := modelBound + 2
  have boundThree : 3 ≤ modelBound := le_max_left _ _
  have extentOne : 1 ≤ extent := (by norm_num : (1 : ℝ) ≤ 4).trans (le_max_left _ _)
  have magnitudeNonnegative : 0 ≤ magnitude := by dsimp only [magnitude]; linarith only [boundThree]
  obtain ⟨matchRatio, _, matchScales⟩ := matchAt matchingAccuracy matchingAccuracyPositive extent magnitude
    (separationRadius orbit sectionTime) (1 / 16) extentOne magnitudeNonnegative (by linarith only [radiusLarge]) (by norm_num)
  let ratioMin := max firstRatio (max matchRatio 128)
  refine ⟨ratioMin, firstRatioTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound boundaryConstant boundaryOne ratioSeparation
  have firstRatioLarge : firstRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have matchRatioLarge : matchRatio ≤ scales.ratio := (le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge)
  have ratio128 : 128 ≤ scales.ratio := (le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge)
  have ratioBound : 2 ≤ scales.ratio := firstRatioTwo.trans firstRatioLarge
  have firstRootLarge : firstRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have matchRootLarge : matchRoot ≤ scaleRoot := (le_max_right _ _).trans rootLarge
  have amplitudePositive : 0 < scales.amplitude := by
    rw [amplitudeIdentity]
    have rootPositive : 0 < scaleRoot := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (firstRootEight.trans firstRootLarge)
    positivity
  have thresholdSmall : threshold ≤ 1 / 8 := (thresholdBound.trans thresholdFirst).trans firstEighth
  have globalGap : 4 * Real.sqrt 2 ≤ (1 / 16 : ℝ) * scales.ratio ^ 2 := by
    have square := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 128) ratio128 2
    norm_num at square
    have sqrtTwo : Real.sqrt 2 ≤ 2 := by norm_num [Real.sqrt_le_iff]
    linarith only [square, sqrtTwo]
  filter_upwards [firstScales scales scaleRoot firstRootLarge amplitudeIdentity firstRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdFirst)
      boundaryConstant boundaryOne ratioSeparation,
    matchScales scales scaleRoot matchRootLarge amplitudeIdentity matchRatioLarge alphaPositive alphaSmall ratioPower globalGap
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdMatch)
      sectionTime boundaryConstant 0 boundaryOne le_rfl ratioSeparation,
    eventually_actual_terminal_finer_initial_data orbit sectionTime initialError errorNonnegative errorSmall radiusLarge separationClose outgoing
      scales amplitudePositive ratio128 alphaPositive,
    refinePhysical scales ratioBound alphaPositive referenceConstant referenceNonnegative,
    eventually_gt_atTop (0 : ℝ)] with frequency first matching finerData physical frequencyPositive
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
  have payload := first count phase dipoleAngle (prepared.enlargeCap capFirst) path index source adjacent terminal prescribed
  dsimp only at payload
  simp only [rawInvariant, centeredInvariant, sizeInvariant] at payload
  obtain ⟨finishPositive, finishQuarter, elapsed, exposure, finishAvailable, unstableLower, hits,
    coarserPhysical, targetData, coarseLift, coarseLiftProperties, coarseLiftPolar, coarseFull⟩ := payload
  obtain ⟨hit, hitPositive, hitBefore, hitIdentity, strictBefore⟩ :=
    hits (coordinate (orbitUnstableShape orbit incomingTime)) targetPositive targetSmall.le
  have savedTarget := targetData
  obtain ⟨targetRadial, targetPhysical, lift, liftProperties, liftPolar,
    shapeContinuous, shapeZero, shapeProfile, stateContinuous, stateZero, stateI, forcingI, targetBounds⟩ := targetData
  have finishInside : finish ∈ Icc 0 path.stop := ⟨finishPositive.le, finishAvailable⟩
  have hitInside : hit ∈ Icc 0 path.stop := ⟨hitPositive.le, hitBefore.trans finishAvailable⟩
  have growthPositive : 0 < growth := by
    have omegaPositive := changed.omega_pos frequencyPositive
      (by change 0 < scales.ratio; linarith only [ratioBound]) (index.val + 1)
    dsimp only [growth]
    positivity
  have exposureAt (time : ℝ) (before : time ≤ finish) :
      changed.seed (index.val + 1) * Real.exp (growth * (time - 0)) ≤ endpoint := by
    rw [← exposure]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (by simpa only [sub_zero] using before) growthPositive.le))
      (changed.seed_pos frequencyPositive (by change 0 < scales.ratio; linarith only [ratioBound]) _).le
  have weakPhysical (current : Fin count) (before : current.val ≤ index.val) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape motion time current| + |stableShape motion time current| ≤ 1 / 4 := by
    rcases lt_or_eq_of_le before with earlier | equal
    · exact ((coarserPhysical time inside current earlier).1.le).trans (by linarith only [radiusQuarter])
    · have same : current = index := Fin.ext equal
      subst current
      exact (targetPhysical time inside).le.trans (by linarith only [targetRadiusQuarter])
  have currentProfile (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.finiteCoordinateSize graph coordinate lift index time + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
        currentMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - 0)) := (targetBounds time inside).1
  have sharpProfile (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.rawSourceCenteredState time index + ‖relativeNormalizedFirstMoment changed motion prepared.reference index time‖ +
        ‖quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index‖ / changed.location (index.val + 1) +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
        currentMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - 0)) := (targetBounds time inside).2
  have currentFullSmall (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.finiteCoordinateSize graph coordinate lift index time + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
        physicalPrecision := by
    have scaled := (le_div_iff₀ (by positivity : 0 < currentMagnitude + 1)).mp (endpointBound.trans endpointMaxPhysical)
    have magnitudeBound : currentMagnitude * endpoint ≤ physicalPrecision := by nlinarith only [scaled, endpointPositive]
    calc
      _ ≤ currentMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - 0)) := currentProfile time inside
      _ = currentMagnitude * (changed.seed (index.val + 1) * Real.exp (growth * (time - 0))) := by ring
      _ ≤ currentMagnitude * endpoint := mul_le_mul_of_nonneg_left (exposureAt time inside.2) currentNonnegative
      _ ≤ physicalPrecision := magnitudeBound
  have targetRefined := physical prepared path factorPositive index nonterminal finish finishInside
    (fun time inside => weakPhysical index le_rfl time inside) lift currentFullSmall
  have physicalAll (current : Fin count) (before : current.val ≤ index.val) (time : ℝ) (inside : time ∈ Icc 0 hit) :
      |unstableShape motion time current| + |stableShape motion time current| ≤ matchRadius := by
    have subset : time ∈ Icc 0 finish := ⟨inside.1, inside.2.trans hitBefore⟩
    rcases lt_or_eq_of_le before with earlier | equal
    · have nonterminalCurrent : current.val + 1 < count := by omega
      have refined := physical prepared path factorPositive current nonterminalCurrent finish finishInside
        (fun time inside => weakPhysical current before time inside) (coarseLift current) (by
          intro time inside
          exact (coarseFull time inside current earlier).trans (min_le_right precision physicalPrecision))
      exact (refined time subset).le
    · have same : current = index := Fin.ext equal
      subst current
      exact (targetRefined time subset).le
  obtain ⟨_, _, entries, extents, sourceProfiles, domains, rateGaps, nearestTiming, sourceTiming⟩ :=
    finerData count phase dipoleAngle prepared path (thresholdSmall.trans (by norm_num)) index source adjacent terminal
  let direction := Complex.exp (Complex.I * (dipoleAngle count : ℂ))
  have actualMatch := matching count phase dipoleAngle (prepared.enlargeCap capMatch) path index nonterminal
    (fun _ => 0) (fun _ => separationRadius orbit sectionTime) (fun _ => direction)
    entries extents (fun _ => magnitude) (by
      intro current finer
      refine ⟨magnitudeNonnegative, ?_⟩
      intro time inside
      simpa only [rawInvariant, centeredInvariant] using sourceProfiles current finer time inside)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) domains (fun _ => 0) (fun _ => rfl)
    nearestTiming sourceTiming (fun _ _ => le_rfl) hit hitInside physicalAll lift liftProperties
    (fun side time inside => liftPolar side time ⟨inside.1, inside.2.trans hitBefore⟩) rateGaps
    (by
      intro time inside
      simpa only [rawInvariant, sizeInvariant] using currentProfile time ⟨inside.1, inside.2.trans hitBefore⟩)
    (by
      intro time inside
      simpa only [rawInvariant, centeredInvariant] using sharpProfile time ⟨inside.1, inside.2.trans hitBefore⟩)
    hitPositive.le ((exposureAt hit hitBefore).trans (endpointBound.trans endpointMaxMatch)) hitIdentity
  refine ⟨finishPositive, finishQuarter, elapsed, exposure, finishAvailable, unstableLower,
    ⟨hit, hitPositive, hitBefore, hitIdentity, strictBefore, ?_⟩,
    coarserPhysical, savedTarget, coarseLift, coarseLiftProperties, coarseLiftPolar, ?_⟩
  · exact ⟨_, actualMatch⟩
  · intro time inside current earlier
    exact (coarseFull time inside current earlier).trans (min_le_left precision physicalPrecision)

end EulerNonuniqueness.Paper
