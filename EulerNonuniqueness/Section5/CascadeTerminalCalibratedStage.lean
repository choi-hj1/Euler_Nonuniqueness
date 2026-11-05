import EulerNonuniqueness.Section5.CascadeTerminalOutgoingSharpProfile
import EulerNonuniqueness.Section5.CascadeTerminalCoefficientAtPrecision
import EulerNonuniqueness.Section5.CascadeOutgoingPhaseAtPrecision
import EulerNonuniqueness.Section5.CascadeActualExitTiming
import EulerNonuniqueness.General.CascadeTimingCalibration
import EulerNonuniqueness.Section6.NormalizedOrbitCoordinateLog
import EulerNonuniqueness.Section5.CascadePhysicalStageData

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_terminal_calibrated_stage
    (eta : ℝ) (etaPositive : 0 < eta) (etaSmall : eta ≤ 1 / 1000)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (sectionTime initialError : ℝ) (modelDerivative : ℝ → ℝ)
    (sectionPositive : 0 < sectionTime) (errorPositive : 0 < initialError) (errorSmall : initialError ≤ 1 / 64)
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
    (numericBudget : 20 * initialError + 83200 / separationRadius orbit sectionTime ^ 2 ≤
      min (min ((eta / 1000) / 4) (1 / 8) / 4) 1 / 5120) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    (∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖) →
    ∃ rootMin ≥ (8 : ℝ), ∃ extent ≥ (4 : ℝ), ∃ endpointMax > (0 : ℝ), endpointMax ≤ 1 ∧
    ∀ endpoint : ℝ, 0 < endpoint → endpoint ≤ endpointMax →
    ∀ᶠ incomingTime : ℝ in atBot,
    incomingTime + 1 < sectionTime ∧ ∃ historyMagnitude ≥ (0 : ℝ),
    ∀ requestedMatchingAccuracy > (0 : ℝ), ∀ coarsePrecision > (0 : ℝ),
    ∃ ratioMin ≥ (4 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ boundaryConstant : ℝ, 1 ≤ boundaryConstant →
    (2 * Real.sqrt 2 + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index source : Fin count, index.val + 1 = source.val → source.val + 1 = count →
    PrescribedCascadePhases {scales with frequency := frequency} orbit sectionTime count phase dipoleAngle →
    ∃ data : CascadePhysicalStageData prepared path index incomingTime extent historyMagnitude (1 / 16)
      initialError (eta / 100) eta requestedMatchingAccuracy,
      0 < data.entry ∧
      |({scales with frequency := frequency} : Scales).omega (index.val + 1) *
        (data.entry - ({scales with frequency := frequency} : Scales).predictedTime sectionTime count (index.val + 1))| ≤ eta / 2 := by
  classical
  have separationPositive : 0 < eta / 10000 := by positivity
  have coefficientPositive : 0 < eta / 1000 := by positivity
  have phasePositive : 0 < eta / 100 := by positivity
  have stageBudget : 20 * initialError + 83200 / separationRadius orbit sectionTime ^ 2 ≤
      min ((1 / 8 : ℝ) / 4) 1 / 5120 := by
    apply numericBudget.trans
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 5120)
    exact min_le_min_right _ (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, stageThreshold, stageThresholdPositive, stageEighth,
    compatible, stageCap, stageCapPositive, stages⟩ :=
    exists_uniform_actual_terminal_outgoing_sharp_profile orbit normalized sectionTime initialError modelDerivative
      sectionPositive errorPositive errorSmall radiusLarge separationClose outgoing transverse earlierMargin
      separationPositive (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1 / 8) stageBudget
  obtain ⟨coefficientThreshold, coefficientThresholdPositive, coefficientEighth, coefficientCap, coefficientCapPositive,
    coefficientFactors⟩ := exists_uniform_actual_terminal_coefficient_at_precision graphAnalytic coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative orbit sectionTime initialError errorPositive.le errorSmall
      radiusLarge separationClose outgoing
  let thresholdMax := min stageThreshold coefficientThreshold
  let rawCap := min stageCap coefficientCap
  have capStage : rawCap ≤ stageCap := min_le_left _ _
  have capCoefficient : rawCap ≤ coefficientCap := min_le_right _ _
  refine ⟨thresholdMax, lt_min stageThresholdPositive coefficientThresholdPositive,
    (min_le_left _ _).trans stageEighth, rawCap, lt_min stageCapPositive coefficientCapPositive, ?_⟩
  intro factor factorPositive factorSmall referenceSeparated
  obtain ⟨incomingMagnitude, incomingNonnegative, stageRoot, stageRootEight, extent, extentFour,
    stageEndpoint, stageEndpointPositive, stageEndpointOne, stageParameters⟩ :=
    stages factorPositive factorSmall referenceSeparated
  obtain ⟨coefficientRoot, coefficientRootEight, coefficientMagnitudes⟩ := coefficientFactors factor factorPositive factorSmall
  obtain ⟨coefficientPrecision, coefficientPrecisionPositive, coefficientEndpoint, coefficientEndpointPositive,
    coefficientEndpointOne, coefficientParameters⟩ := coefficientMagnitudes incomingMagnitude incomingMagnitude
      incomingNonnegative incomingNonnegative (eta / 1000) coefficientPositive numericBudget
  obtain ⟨phaseEndpoint, phaseEndpointPositive, phaseEndpointOne, phaseParameters⟩ :=
    exists_uniform_actual_outgoing_phase_at_precision graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative orbit normalized sectionTime factor factorPositive incomingMagnitude incomingNonnegative
      (eta / 100) phasePositive
  let rootMin := max stageRoot coefficientRoot
  let endpointMax := min stageEndpoint (min coefficientEndpoint phaseEndpoint)
  have endpointPositive : 0 < endpointMax := lt_min stageEndpointPositive (lt_min coefficientEndpointPositive phaseEndpointPositive)
  have endpointStage : endpointMax ≤ stageEndpoint := min_le_left _ _
  have endpointCoefficient : endpointMax ≤ coefficientEndpoint := (min_le_right _ _).trans (min_le_left _ _)
  have endpointPhase : endpointMax ≤ phaseEndpoint := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨rootMin, stageRootEight.trans (le_max_left _ _), extent, extentFour, endpointMax, endpointPositive,
    endpointStage.trans stageEndpointOne, ?_⟩
  intro endpoint endpointPositive' endpointBound
  have modelTail : ∀ᶠ incomingTime : ℝ in atBot,
      |Real.log (coordinate (orbitUnstableShape orbit incomingTime)) / (2 * Real.sqrt 2) - incomingTime| ≤ eta / 1000 := by
    have limit := normalizedSeparatingOrbit_coordinate_log_time_tendsto coordinateZero coordinateDerivative orbit normalized
    filter_upwards [limit.eventually (Metric.ball_mem_nhds (0 : ℝ) coefficientPositive)] with incomingTime bound
    exact (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using bound.le)
  filter_upwards [stageParameters endpoint endpointPositive' (endpointBound.trans endpointStage), phaseParameters, modelTail]
    with incomingTime stageAt phaseAt modelBound
  obtain ⟨sectionAfter, levelPositive, levelSmall, matchingTolerance, matchingTolerancePositive,
    historyMagnitude, historyNonnegative, stageScales⟩ := stageAt
  refine ⟨sectionAfter, historyMagnitude, historyNonnegative, ?_⟩
  intro requestedMatchingAccuracy matchingPositive coarsePrecision coarsePositive
  let selectedPrecision := min coarsePrecision coefficientPrecision
  have selectedPositive : 0 < selectedPrecision := lt_min coarsePositive coefficientPrecisionPositive
  obtain ⟨stageRatio, stageRatioTwo, stageFrequencies⟩ :=
    stageScales requestedMatchingAccuracy matchingPositive selectedPrecision selectedPositive
  obtain ⟨coefficientRatio, coefficientRatioTwo, coefficientFrequencies⟩ :=
    coefficientParameters endpoint endpointPositive' (endpointBound.trans endpointCoefficient)
      (coordinate (orbitUnstableShape orbit incomingTime)) levelPositive
  let ratioMin := max 4 (max stageRatio coefficientRatio)
  refine ⟨ratioMin, le_max_left _ _, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound boundaryConstant boundaryOne ratioSeparation
  have ratioFour : 4 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioTwo : 2 ≤ scales.ratio := (by norm_num : (2 : ℝ) ≤ 4).trans ratioFour
  have stageRatioLarge : stageRatio ≤ scales.ratio := (le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge)
  have coefficientRatioLarge : coefficientRatio ≤ scales.ratio := (le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge)
  have stageRootLarge : stageRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have coefficientRootLarge : coefficientRoot ≤ scaleRoot := (le_max_right _ _).trans rootLarge
  have stageThresholdBound : threshold ≤ stageThreshold := thresholdBound.trans (min_le_left _ _)
  have coefficientThresholdBound : threshold ≤ coefficientThreshold := thresholdBound.trans (min_le_right _ _)
  filter_upwards [stageFrequencies scales scaleRoot stageRootLarge amplitudeIdentity stageRatioLarge alphaPositive alphaSmall
      ratioPower referenceConstant referenceNonnegative referenceAmplitude threshold stageThresholdBound boundaryConstant boundaryOne ratioSeparation,
    coefficientFrequencies scales scaleRoot coefficientRootLarge amplitudeIdentity coefficientRatioLarge alphaPositive alphaSmall
      ratioPower referenceConstant referenceNonnegative referenceAmplitude threshold coefficientThresholdBound boundaryConstant boundaryOne ratioSeparation,
    phaseAt scales ratioTwo alphaPositive referenceConstant referenceNonnegative,
    eventually_gt_atTop (0 : ℝ)] with frequency stage coefficientEstimate phaseEstimate frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index source adjacent terminal prescribed
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let growth := 2 * Real.sqrt 2 * omega
  let finish := Real.log (endpoint / changed.seed (index.val + 1)) / growth
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioFour]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
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
    targetData, coarseLift, coarseLiftProperties, coarseLiftPolar, coarseFull⟩ := payload
  obtain ⟨lift, liftProperties, liftPolar, fullProfile⟩ := targetData
  obtain ⟨hit, hitPositive, hitBefore, hitIdentity, strictBefore, weakQuarter, sharpProfile, exposureOne,
    rotation, canonical, rotationNorm, matchingClose, compactAvailable, directionNorm, contact, contactBracket,
    contactInside, firstSeparation, earlierStrict, passageTiming, distance, firstError, secondError,
    projection, centerUpper, slowProfile, domainBounds⟩ := hitData
  have hitInside : hit ∈ Icc 0 path.stop := ⟨hitPositive.le, hitBefore.trans finishAvailable⟩
  have hitSubset {time : ℝ} (inside : time ∈ Icc 0 hit) : time ∈ Icc 0 finish :=
    ⟨inside.1, inside.2.trans hitBefore⟩
  have exposureHit : changed.seed (index.val + 1) * Real.exp (growth * hit) ≤ endpoint := by
    have growthNonnegative : 0 ≤ growth := by dsimp only [growth]; positivity
    calc
      _ ≤ changed.seed (index.val + 1) * Real.exp (growth * finish) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hitBefore growthNonnegative))
          (changed.seed_pos frequencyPositive ratioPositive _).le
      _ = endpoint := exposure
  have coefficientResult := coefficientEstimate count phase dipoleAngle (prepared.enlargeCap capCoefficient) path index source
    adjacent terminal prescribed hit hitInside hitIdentity weakQuarter lift
    (fun side => (liftProperties side).1.continuousOn) (fun side => (liftProperties side).2)
    (fun side time inside => liftPolar side time (hitSubset inside))
    (by intro time inside; simpa only [rawInvariant, sizeInvariant] using fullProfile time (hitSubset inside))
    (by intro time inside; simpa only [rawInvariant, centeredInvariant] using sharpProfile time inside)
    coarseLift
    (by
      intro current before time inside
      have bound := (coarseFull time (hitSubset inside) current before).trans (min_le_right _ _)
      simpa only [rawInvariant, sizeInvariant] using bound)
    exposureHit
  dsimp only at coefficientResult
  let coefficient := Real.exp (-growth * hit) *
    (referenceStraightenedShape motion graph coordinate index hit -
      referenceStraightenedShape prepared.reference graph coordinate index hit).1 / changed.seed (index.val + 1)
  have coefficientClose : |coefficient - 1| ≤ eta / 1000 := coefficientResult.1
  have coefficientPositive' : 0 < coefficient := coefficientResult.2.1
  have exitIdentity : changed.seed (index.val + 1) * coefficient * Real.exp (growth * hit) =
      coordinate (orbitUnstableShape orbit incomingTime) := coefficientResult.2.2
  have passageBound : |omega * (contact - hit) - (sectionTime - incomingTime)| ≤ 2 * (eta / 10000) := by
    have scaled := mul_le_mul_of_nonneg_left passageTiming omegaPositive.le
    rw [← abs_of_pos omegaPositive, ← abs_mul] at scaled
    have identity : omega * (contact - (hit + (sectionTime - incomingTime) / omega)) =
        omega * (contact - hit) - (sectionTime - incomingTime) := by field_simp; ring
    rw [identity] at scaled
    have cancel : omega * (2 * (eta / 10000) / omega) = 2 * (eta / 10000) := by field_simp; ring
    change |omega * (contact - hit) - (sectionTime - incomingTime)| ≤
      |omega| * (2 * (eta / 10000) / omega) at scaled
    rw [abs_of_pos omegaPositive, cancel] at scaled
    exact scaled
  have budgets := EulerNonuniqueness.cascade_timing_fixed_budgets etaPositive etaSmall ratioFour
  have phaseResult := phaseEstimate prepared path prescribed index (by omega) hit hitInside 0 contact endpoint
    endpointPositive' (endpointBound.trans endpointPhase) (fun time inside => weakQuarter index le_rfl time inside)
    lift (fun side => (liftProperties side).1.continuousOn) (fun side => (liftProperties side).2)
    (fun side time inside => liftPolar side time (hitSubset inside))
    (by intro time inside; simpa only [sub_zero] using fullProfile time (hitSubset inside))
    (by simpa only [sub_zero] using exposureHit)
    (passageBound.trans budgets.2.2.2.2.2.1) rotation canonical
  dsimp only at phaseResult
  obtain ⟨phaseIdentity, winding, phaseBound⟩ := phaseResult
  have clockBound := changed.terminal_actual_exit_timing_bound frequencyPositive ratioFour
    (show index.val + 1 + 1 = count by omega) sectionTime hit contact incomingTime
    (coordinate (orbitUnstableShape orbit incomingTime)) coefficient (eta / 1000)
    (2 * (eta / 10000)) (eta / 1000) levelPositive coefficientPositive' exitIdentity coefficientPositive.le
    (by linarith only [etaSmall]) coefficientClose passageBound modelBound
  have clockHalf : |omega * (contact - changed.predictedTime sectionTime count (index.val + 1))| ≤ eta / 2 := by
    apply EulerNonuniqueness.cascade_timing_recurrence_half_bound (next := 0) (phaseError := 0)
      etaPositive etaSmall ratioFour (by simpa using etaPositive.le) (by simpa only [abs_zero] using phasePositive.le)
      (le_refl (eta / 1000)) budgets.2.2.2.2.2.2.1 (le_refl (eta / 1000))
    simpa only [abs_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, add_zero] using clockBound
  let outgoingPhase := lift 0 hit - orbit.phase incomingTime + orbit.limitingDipoleAngle
  refine ⟨{
    entry := contact
    entryInside := ⟨hitPositive.le.trans contactInside.1, contactInside.2⟩
    firstSeparation := firstSeparation
    direction := rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
    directionNorm := directionNorm
    outgoingPhase := outgoingPhase
    directionPhase := phaseIdentity.symm
    firstError := firstError
    secondError := secondError
    outgoingProjection := projection
    centerUpper := centerUpper
    extents := ?_
    domains := ?_
    sharp := slowProfile
    winding := winding
    wrappedPhase := phaseBound
    timing := clockHalf.trans (by linarith only [etaPositive])
    previousMatch := ?_ }, hitPositive.trans_le contactInside.1, clockHalf⟩
  · intro time inside patch
    exact ⟨(domainBounds time inside patch).1, (domainBounds time inside patch).2.1⟩
  · intro time inside patch
    exact ⟨(domainBounds time inside patch).2.2.1, (domainBounds time inside patch).2.2.2⟩
  · intro _
    refine ⟨hit, ⟨hitPositive.le, contactInside.1⟩, rotation, rotationNorm, ?_⟩
    exact matchingClose.le.trans (min_le_right _ _)

end EulerNonuniqueness.Paper
