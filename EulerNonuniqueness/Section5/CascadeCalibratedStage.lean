import EulerNonuniqueness.Section5.CascadeOutgoingSharpProfile
import EulerNonuniqueness.Section5.CascadeCoefficientAtPrecision
import EulerNonuniqueness.Section5.CascadeOutgoingPhaseAtPrecision
import EulerNonuniqueness.Section5.CascadeActualExitTiming
import EulerNonuniqueness.General.CascadeTimingCalibration
import EulerNonuniqueness.Section6.NormalizedOrbitCoordinateLog
import EulerNonuniqueness.Section5.CascadePhysicalStageData

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private def calibratedStageTime {count : ℕ} (entry : Fin count → ℝ) (index : ℕ) : ℝ :=
  if h : index - 1 < count then entry ⟨index - 1, h⟩ else 0

private theorem calibratedStageTime_apply {count : ℕ} (entry : Fin count → ℝ) (index : Fin count) :
    calibratedStageTime entry (index.val + 1) = entry index := by
  simp only [calibratedStageTime, Nat.add_sub_cancel_right, index.isLt, dite_true]

private theorem calibrated_contact_error {omega hit contact modelSection incoming accuracy : ℝ}
    (omegaPositive : 0 < omega)
    (bound : |contact - (hit + (modelSection - incoming) / omega)| ≤ 2 * accuracy / omega) :
    |omega * (contact - hit) - (modelSection - incoming)| ≤ 2 * accuracy := by
  have scaled := mul_le_mul_of_nonneg_left bound omegaPositive.le
  have identity : omega * (contact - (hit + (modelSection - incoming) / omega)) =
      omega * (contact - hit) - (modelSection - incoming) := by field_simp; ring
  calc
    _ = omega * |contact - (hit + (modelSection - incoming) / omega)| := by
      rw [← identity, abs_mul, abs_of_pos omegaPositive]
    _ ≤ omega * (2 * accuracy / omega) := scaled
    _ = 2 * accuracy := by field_simp

theorem exists_uniform_actual_calibrated_stage
    {eta : ℝ} (etaPositive : 0 < eta) (etaSmall : eta ≤ 1 / 1000)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (sectionTime initialError : ℝ) (modelDerivative : ℝ → ℝ)
    (sectionPositive : 0 < sectionTime) (errorPositive : 0 < initialError) (errorSmall : initialError ≤ 1 / 64)
    (radiusLarge : 2048 ≤ separationRadius orbit sectionTime)
    (transverse : ∀ time ∈ Icc (sectionTime - 1) (sectionTime + 1),
      HasDerivAt (separationRadius orbit) (modelDerivative time) time ∧ 1 ≤ modelDerivative time)
    (earlierMargin : ∀ time ≤ sectionTime - 1,
      separationRadius orbit time ≤ separationRadius orbit sectionTime - 1)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ initialError / 2)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re)
    (numericBudget : 20 * initialError + 83200 / separationRadius orbit sectionTime ^ 2 ≤
      min ((min (((eta / 1000) / 4) / 2) (1 / 8)) / 4) 1 / 5120) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    (∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖) →
    ∃ extent ≥ (4 : ℝ), ∃ rootMin ≥ (8 : ℝ), ∃ endpointMax > (0 : ℝ), endpointMax ≤ 1 ∧
    ∀ endpoint : ℝ, 0 < endpoint → endpoint ≤ endpointMax →
    ∀ᶠ incomingTime : ℝ in atBot, incomingTime + 1 < sectionTime ∧
    ∃ stageTolerance > (0 : ℝ), ∃ historyMagnitude ≥ (0 : ℝ),
    ∀ matchingAccuracy : ℝ, 0 < matchingAccuracy → ∀ priorExtent priorMagnitude : ℝ,
    1 ≤ priorExtent → 0 ≤ priorMagnitude → ∃ ratioMin ≥ (4 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ boundaryConstant : ℝ, 1 ≤ boundaryConstant →
    ((1 / 16 : ℝ) * scales.ratio + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    PrescribedCascadePhases {scales with frequency := frequency} orbit sectionTime count phase dipoleAngle →
    ∀ (index : Fin count) (nonterminal : index.val + 1 < count), index.val + 2 < count →
    ∀ prior : ∀ source : Fin count, index.val < source.val →
      CascadePhysicalStageData prepared path source incomingTime priorExtent priorMagnitude (1 / 16) initialError
        (eta / 100) eta stageTolerance,
    let drive : Fin count := ⟨index.val + 1, nonterminal⟩
    let driver := prior drive (Nat.lt_succ_self index.val)
    (∀ source : Fin count, ∀ finer : index.val < source.val, (prior source finer).entry ≤ driver.entry) →
    driver.entry ≤ 1 / 2 →
    (∀ source : Fin count, index.val < source.val →
      2 * (2 * Real.sqrt 2 * ({scales with frequency := frequency} : Scales).omega (index.val + 1)) ≤
        (1 / 16 : ℝ) * ({scales with frequency := frequency} : Scales).omega (source.val + 1)) →
    ∃ data : CascadePhysicalStageData prepared path index incomingTime extent historyMagnitude (1 / 16) initialError
      (eta / 100) eta matchingAccuracy,
      driver.entry < data.entry ∧
      |({scales with frequency := frequency} : Scales).omega (index.val + 1) *
        (data.entry - ({scales with frequency := frequency} : Scales).predictedTime sectionTime count (index.val + 1))| ≤ eta / 2 := by
  classical
  have phasePositive : 0 < eta / 100 := by positivity
  have errorBudgetPositive : 0 < eta / 1000 := by positivity
  have separationPositive : 0 < eta / 10000 := by positivity
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, _, _, stageThreshold, stageThresholdPositive, stageEighth, _, stageCap, stageCapPositive,
    stageFactors⟩ := exists_uniform_actual_outgoing_sharp_profile orbit normalized sectionTime initialError modelDerivative
      sectionPositive errorPositive errorSmall ((by norm_num : (512 : ℝ) ≤ 2048).trans radiusLarge) transverse earlierMargin
      separationClose outgoing separationPositive (1 / 16) (by norm_num) (by norm_num)
  obtain ⟨coefficientThreshold, coefficientThresholdPositive, _, coefficientCap, coefficientCapPositive,
    coefficientFactors⟩ := exists_uniform_actual_coefficient_at_precision graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  let thresholdMax := min stageThreshold coefficientThreshold
  let rawCap := min stageCap coefficientCap
  have thresholdStage : thresholdMax ≤ stageThreshold := min_le_left _ _
  have thresholdCoefficient : thresholdMax ≤ coefficientThreshold := min_le_right _ _
  have capStage : rawCap ≤ stageCap := min_le_left _ _
  have capCoefficient : rawCap ≤ coefficientCap := min_le_right _ _
  refine ⟨thresholdMax, lt_min stageThresholdPositive coefficientThresholdPositive, thresholdStage.trans stageEighth,
    rawCap, lt_min stageCapPositive coefficientCapPositive, ?_⟩
  intro factor factorPositive factorSmall referenceSeparated
  obtain ⟨currentMagnitude, currentOne, _, _, _, stageRoot, stageRootEight, extent, extentFour,
    stageEndpoint, stageEndpointPositive, stageEndpointOne, stageParameters⟩ := stageFactors factorPositive factorSmall referenceSeparated
  have currentNonnegative : 0 ≤ currentMagnitude := zero_le_one.trans currentOne
  obtain ⟨coefficientRoot, _, coefficientMagnitudes⟩ := coefficientFactors factor factorPositive factorSmall
  obtain ⟨coarsePrecision, coarsePositive, coefficientEndpoint, coefficientEndpointPositive, _, coefficientParameters⟩ :=
    coefficientMagnitudes currentMagnitude currentMagnitude currentNonnegative currentNonnegative (eta / 1000) errorBudgetPositive
  obtain ⟨phaseEndpoint, phaseEndpointPositive, _, phaseTail⟩ :=
    exists_uniform_actual_outgoing_phase_at_precision graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative
      coordinateDerivative orbit normalized sectionTime factor factorPositive currentMagnitude currentNonnegative (eta / 100) phasePositive
  let rootMin := max stageRoot coefficientRoot
  let endpointMax := min stageEndpoint (min coefficientEndpoint phaseEndpoint)
  have endpointMaxPositive : 0 < endpointMax := by dsimp only [endpointMax]; positivity
  have endpointStage : endpointMax ≤ stageEndpoint := min_le_left _ _
  have endpointCoefficient : endpointMax ≤ coefficientEndpoint := (min_le_right _ _).trans (min_le_left _ _)
  have endpointPhase : endpointMax ≤ phaseEndpoint := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨extent, extentFour, rootMin, stageRootEight.trans (le_max_left _ _), endpointMax,
    endpointMaxPositive, endpointStage.trans stageEndpointOne, ?_⟩
  intro endpoint endpointPositive endpointBound
  have logLimit := (normalizedSeparatingOrbit_coordinate_log_time_tendsto coordinateZero coordinateDerivative orbit normalized).abs
  simp only [abs_zero] at logLimit
  filter_upwards [stageParameters endpoint endpointPositive (endpointBound.trans endpointStage), phaseTail,
    logLimit.eventually (eventually_lt_nhds errorBudgetPositive)] with incomingTime stageAt phaseAt logSmall
  obtain ⟨sectionAfter, levelPositive, levelSmall, stageTolerance, stageTolerancePositive, historyMagnitude,
    historyNonnegative, stageAccuracy⟩ := stageAt
  refine ⟨sectionAfter, stageTolerance, stageTolerancePositive, historyMagnitude, historyNonnegative, ?_⟩
  intro matchingAccuracy matchingPositive priorExtent priorMagnitude priorExtentOne priorNonnegative
  obtain ⟨stageRatio, _, stageScales⟩ := stageAccuracy matchingAccuracy matchingPositive coarsePrecision coarsePositive
    priorExtent priorMagnitude (separationRadius orbit sectionTime) priorExtentOne priorNonnegative
    (by linarith only [radiusLarge]) (eta / 100) phasePositive.le
  obtain ⟨coefficientRatio, _, coefficientScales⟩ := coefficientParameters endpoint endpointPositive
    (endpointBound.trans endpointCoefficient) (coordinate (orbitUnstableShape orbit incomingTime)) levelPositive
    priorExtent priorMagnitude (separationRadius orbit sectionTime) (1 / 16) priorExtentOne priorNonnegative
    (by linarith only [radiusLarge]) (by norm_num) (by norm_num) initialError errorSmall
  let ratioMin := max 4 (max stageRatio coefficientRatio)
  refine ⟨ratioMin, le_max_left _ _, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound boundaryConstant boundaryOne controlledSeparation
  have ratioFour : 4 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioTwo : 2 ≤ scales.ratio := (by norm_num : (2 : ℝ) ≤ 4).trans ratioFour
  have stageRatioLarge : stageRatio ≤ scales.ratio := (le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge)
  have coefficientRatioLarge : coefficientRatio ≤ scales.ratio := (le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge)
  have stageRootLarge : stageRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have coefficientRootLarge : coefficientRoot ≤ scaleRoot := (le_max_right _ _).trans rootLarge
  have budgets := EulerNonuniqueness.cascade_timing_fixed_budgets etaPositive etaSmall ratioFour
  filter_upwards [stageScales scales scaleRoot stageRootLarge amplitudeIdentity stageRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdStage)
      boundaryConstant eta boundaryOne etaPositive.le budgets.2.2.2.2.1 controlledSeparation,
    coefficientScales scales scaleRoot coefficientRootLarge amplitudeIdentity coefficientRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdCoefficient)
      orbit sectionTime boundaryConstant eta boundaryOne etaPositive.le controlledSeparation,
    phaseAt scales ratioTwo alphaPositive referenceConstant referenceNonnegative
      (threshold := threshold) (scaleRoot := scaleRoot) (boundaryConstant := boundaryConstant),
    eventually_ge_atTop (max 1 (16 * separationRadius orbit sectionTime))]
    with frequency stage coefficientEstimate phaseEstimate frequencyLarge
  intro count phase dipoleAngle shapeRadius monitor prepared path prescribed index nonterminal driveNonterminal prior
  dsimp only
  intro timeOrder originBound sourceRates
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let drive : Fin count := ⟨index.val + 1, nonterminal⟩
  have driveFiner : index.val < drive.val := by dsimp only [drive]; omega
  let driver := prior drive driveFiner
  let entry : Fin count → ℝ := fun source => if h : index.val < source.val then (prior source h).entry else 0
  let direction : Fin count → ℂ := fun source => if h : index.val < source.val then (prior source h).direction else 1
  let initialDistance : Fin count → ℝ := fun _ => separationRadius orbit sectionTime
  let magnitude : Fin count → ℝ := fun _ => priorMagnitude
  let actualTime := calibratedStageTime entry
  let origin := entry drive
  let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  let finish := origin + Real.log (endpoint / changed.seed (index.val + 1)) / growth
  have entryEq (source : Fin count) (finer : index.val < source.val) : entry source = (prior source finer).entry := by
    simp only [entry, dif_pos finer]
  have directionEq (source : Fin count) (finer : index.val < source.val) : direction source = (prior source finer).direction := by
    simp only [direction, dif_pos finer]
  have timeIdentity (source : Fin count) : actualTime (source.val + 1) = entry source := calibratedStageTime_apply entry source
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le ((le_max_left _ _).trans frequencyLarge)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioTwo]
  have omegaPositive (source : Fin count) : 0 < changed.omega (source.val + 1) := changed.omega_pos frequencyPositive ratioPositive _
  have growthPositive : 0 < growth := by have actual := omegaPositive index; dsimp only [growth]; positivity
  have distanceSmall (source : Fin count) : separationRadius orbit sectionTime ≤ changed.omega (source.val + 1) / 16 := by
    have lower := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioTwo]) (source.val + 1)
    have bound : 16 * separationRadius orbit sectionTime ≤ frequency := (le_max_right _ _).trans frequencyLarge
    linarith only [lower, bound]
  have sourceTiming (source : Fin count) (finer : index.val < source.val) :
      |actualTime (source.val + 1) - changed.predictedTime sectionTime count (source.val + 1)| ≤ eta / changed.omega (source.val + 1) := by
    rw [timeIdentity, entryEq source finer]
    apply (le_div_iff₀ (omegaPositive source)).mpr
    have timing : |changed.omega (source.val + 1) *
        ((prior source finer).entry - changed.predictedTime sectionTime count (source.val + 1))| ≤ eta :=
      (prior source finer).timing
    rw [abs_mul, abs_of_pos (omegaPositive source)] at timing
    simpa only [mul_comm] using timing
  have nearestTiming : |actualTime (index.val + 2) - changed.predictedTime sectionTime count (index.val + 2)| ≤
      eta / changed.omega (index.val + 2) := by
    simpa only [drive, Nat.add_assoc] using sourceTiming drive driveFiner
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time current patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  have sizeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateSize graph coordinate = prepared.finiteCoordinateSize graph coordinate := rfl
  have entries (source : Fin count) (finer : index.val < source.val) :
      0 ≤ entry source ∧ entry source ≤ path.stop ∧ 512 ≤ initialDistance source ∧
      initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
      ‖firstDipoleSeparation motion (entry source) source - (changed.length (source.val + 1) : ℂ) * direction source‖ ≤
        changed.length (source.val + 1) / 64 ∧
      ‖secondDipoleSeparation motion (entry source) source - (changed.length (source.val + 1) : ℂ) * (-direction source)‖ ≤
        changed.length (source.val + 1) / 64 ∧
      (3 / 4 : ℝ) * changed.length (source.val + 1) * initialDistance source ≤
        (Complex.I * star (direction source) * (firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source)).re ∧
      ‖firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source‖ ≤
        (5 / 4 : ℝ) * changed.length (source.val + 1) * initialDistance source := by
    have first := (prior source finer).firstError
    have second := (prior source finer).secondError
    have weak := mul_le_mul_of_nonneg_right errorSmall (changed.length_pos (source.val + 1)).le
    refine ⟨?_, ?_, by dsimp only [initialDistance]; linarith only [radiusLarge], distanceSmall source, ?_, ?_, ?_, ?_, ?_⟩
    · rw [entryEq source finer]; exact (prior source finer).entryInside.1
    · rw [entryEq source finer]; exact (prior source finer).entryInside.2
    · rw [directionEq source finer]; exact (prior source finer).directionNorm
    · rw [entryEq source finer, directionEq source finer]
      exact first.trans (by simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using weak)
    · rw [entryEq source finer, directionEq source finer]
      exact second.trans (by simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using weak)
    · simpa only [entryEq source finer, directionEq source finer] using (prior source finer).outgoingProjection
    · simpa only [entryEq source finer, directionEq source finer] using (prior source finer).centerUpper
  have extents (source : Fin count) (finer : index.val < source.val) (time : ℝ) (inside : time ∈ Icc 0 (entry source)) :
      (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤ priorExtent * changed.length (source.val + 1)) ∧
      (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤ priorExtent * changed.length (source.val + 1)) := by
    have member : time ∈ Icc 0 (prior source finer).entry := by simpa only [entryEq source finer] using inside
    exact ⟨fun patch => ((prior source finer).extents time member patch).2, fun patch => ((prior source finer).extents time member patch).1⟩
  have profiles (source : Fin count) (finer : index.val < source.val) : 0 ≤ magnitude source ∧
      ∀ time ∈ Icc 0 (entry source), prepared.rawSourceCenteredState time source +
        ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
        ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch ≤
        magnitude source * Real.exp ((1 / 16 : ℝ) * changed.omega (source.val + 1) * (time - entry source)) := by
    refine ⟨priorNonnegative, ?_⟩
    intro time inside
    simpa only [entryEq source finer] using (prior source finer).sharp time (by simpa only [entryEq source finer] using inside)
  have domains (source : Fin count) (finer : index.val < source.val) (time : ℝ) (inside : time ∈ Icc 0 (entry source)) (patch : Fin 4) :
      motion.domain time source patch ⊆ Metric.closedBall (quadrupoleCenter motion time source) (priorExtent * changed.length (source.val + 1)) := by
    exact ((prior source finer).domains time (by simpa only [entryEq source finer] using inside) patch).1
  have entryOrder (source : Fin count) (finer : index.val < source.val) : entry source ≤ entry drive := by
    rw [entryEq source finer, entryEq drive driveFiner]
    exact timeOrder source finer
  have originSmall : entry drive ≤ 1 / 2 := by simpa only [entryEq drive driveFiner] using originBound
  have previousMatches (source : Fin count) (finer : index.val < source.val) (sourceNonterminal : source.val + 1 < count) :
      ∃ previousHit ∈ Icc 0 (entry source), ∃ previousRotation : ℂ, ‖previousRotation‖ = 1 ∧
        ‖cascadeNormalizedPointPositions changed motion source previousHit previousRotation 0 -
          centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ stageTolerance := by
    simpa only [entryEq source finer] using (prior source finer).previousMatch sourceNonterminal
  have driverDirection : direction drive = Complex.exp (Complex.I * (driver.outgoingPhase : ℂ)) := by
    rw [directionEq drive driveFiner]; exact driver.directionPhase
  have driverPhase : |driver.outgoingPhase - dipoleAngle (drive.val + 1) + changed.omega (drive.val + 1) *
      (entry drive - changed.predictedTime sectionTime count (drive.val + 1)) - (driver.winding : ℝ) * Real.pi| ≤ eta / 100 := by
    simpa only [entryEq drive driveFiner] using driver.wrappedPhase
  have firstDriver : ‖firstDipoleSeparation motion (entry drive) drive - (changed.length (drive.val + 1) : ℂ) * direction drive‖ ≤
      initialError * changed.length (drive.val + 1) := by
    simpa only [entryEq drive driveFiner, directionEq drive driveFiner] using driver.firstError
  have secondDriver : ‖secondDipoleSeparation motion (entry drive) drive - (changed.length (drive.val + 1) : ℂ) * (-direction drive)‖ ≤
      initialError * changed.length (drive.val + 1) := by
    simpa only [entryEq drive driveFiner, directionEq drive driveFiner] using driver.secondError
  have windowSmall : min (((eta / 1000) / 4) / 2) (1 / 8) ≤ (1 / 32 : ℝ) := by
    have lower := min_le_left (((eta / 1000) / 4) / 2) (1 / 8 : ℝ)
    linarith only [lower, etaSmall]
  have positiveNumeric : 20 * initialError + 83200 / separationRadius orbit sectionTime ^ 2 ≤ min ((1 / 32 : ℝ) / 4) 1 / 5120 :=
    numericBudget.trans (div_le_div_of_nonneg_right
      (min_le_min (div_le_div_of_nonneg_right windowSmall (by norm_num : (0 : ℝ) ≤ 4)) le_rfl) (by norm_num))
  have payload := stage count phase dipoleAngle (prepared.enlargeCap capStage) path prescribed index nonterminal driveNonterminal
    entry initialDistance direction entries extents magnitude (by simpa only [rawInvariant, centeredInvariant] using profiles)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) domains actualTime timeIdentity nearestTiming sourceTiming entryOrder originSmall sourceRates
    previousMatches driver.outgoingPhase driver.winding driverDirection driverPhase radiusLarge positiveNumeric firstDriver secondDriver
  dsimp only at payload
  simp only [rawInvariant, centeredInvariant, sizeInvariant] at payload
  obtain ⟨finishPositive, _, _, _, exposure, _, finishAvailable, _, hitData, weakPhysical, targetData, coarseLift, _, _, coarseFull⟩ := payload
  obtain ⟨hit, hitAfter, hitBefore, hitIdentity, _, _, rotation, canonical, rotationNorm, matchingClose,
    compactAvailable, directionNorm, contact, contactInside, firstSeparation, _, contactTiming, _, firstError,
    secondError, outgoingProjection, centerUpper, contactDomains, slowProfile⟩ := hitData
  obtain ⟨lift, liftProperties, liftPolar, _, _, _, _, targetBounds⟩ := targetData
  have originNonnegative : 0 ≤ origin := (entries drive driveFiner).1
  have hitPositive : 0 < hit := lt_of_le_of_lt originNonnegative hitAfter
  have hitInside : hit ∈ Icc 0 path.stop := ⟨hitPositive.le, hitBefore.trans finishAvailable⟩
  have contactAfter : hit < contact := by
    have lagPositive : 0 < (sectionTime - incomingTime - 1) / changed.omega (index.val + 1) :=
      div_pos (by linarith only [sectionAfter]) (omegaPositive index)
    exact (lt_add_of_pos_right hit lagPositive).trans_le contactInside.1
  have contactBefore : contact ≤ path.stop := contactInside.2.trans compactAvailable
  have exposureHit : changed.seed (index.val + 1) * Real.exp (growth * (hit - origin)) ≤ endpoint := by
    rw [← exposure]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hitBefore origin) growthPositive.le))
      (changed.seed_pos frequencyPositive ratioPositive _).le
  have weakHit (current : Fin count) (before : current.val ≤ index.val) (time : ℝ) (inside : time ∈ Icc 0 hit) :
      |unstableShape motion time current| + |stableShape motion time current| ≤ 1 / 4 :=
    weakPhysical time ⟨inside.1, inside.2.trans hitBefore⟩ current before
  have coefficient := coefficientEstimate count phase dipoleAngle (prepared.enlargeCap capCoefficient) prescribed path index nonterminal
    driveNonterminal entry initialDistance direction entries extents magnitude (by simpa only [rawInvariant, centeredInvariant] using profiles)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) domains actualTime timeIdentity nearestTiming sourceTiming entryOrder
    driver.outgoingPhase driver.winding driverDirection radiusLarge numericBudget firstDriver secondDriver
    hit hitInside hitAfter.le hitIdentity weakHit lift (fun side => (liftProperties side).1.continuousOn)
    (fun side => (liftProperties side).2) (fun side time inside => liftPolar side time ⟨inside.1, inside.2.trans hitBefore⟩) sourceRates
    (by
      intro time inside
      simpa only [rawInvariant, sizeInvariant] using (targetBounds time ⟨inside.1, inside.2.trans hitBefore⟩).1)
    (by
      intro time inside
      simpa only [rawInvariant, centeredInvariant] using (targetBounds time ⟨inside.1, inside.2.trans hitBefore⟩).2)
    coarseLift (by
      intro current earlier time inside
      simpa only [rawInvariant, sizeInvariant] using coarseFull time ⟨inside.1, inside.2.trans hitBefore⟩ current earlier)
    exposureHit
  dsimp only at coefficient
  let next := changed.omega (drive.val + 1) * (origin - changed.predictedTime sectionTime count (drive.val + 1))
  let previousPhaseError := driver.outgoingPhase - dipoleAngle (drive.val + 1) + next - (driver.winding : ℝ) * Real.pi
  let actualQ := (referenceStraightenedShape motion graph coordinate index hit - referenceStraightenedShape prepared.reference graph coordinate index hit).1
  let actualCoefficient := Real.exp (-growth * (hit - origin)) * actualQ / changed.seed (index.val + 1)
  have nextBound : |next| ≤ eta := by simpa only [next, origin, entryEq drive driveFiner] using driver.timing
  have previousPhaseBound : |previousPhaseError| ≤ eta / 100 := driverPhase
  have coefficientClose : |actualCoefficient - Real.cos (2 * (1 + changed.ratio⁻¹) * next - 2 * previousPhaseError)| ≤ eta / 1000 := by
    rw [← coefficient.1]
    exact coefficient.2.1
  have coefficientPositive : 0 < actualCoefficient := coefficient.2.2.1
  have exitIdentity : changed.seed (index.val + 1) * actualCoefficient * Real.exp (growth * (hit - origin)) =
      coordinate (orbitUnstableShape orbit incomingTime) := coefficient.2.2.2
  have normalizedContact := calibrated_contact_error (omegaPositive index) contactTiming
  have passageBound : |changed.omega (index.val + 1) * (contact - hit) - (sectionTime - incomingTime)| ≤ eta / 1000 :=
    normalizedContact.trans budgets.2.2.2.2.2.2.1
  have effectiveSmall : eta / 1000 + 2 * |previousPhaseError| ≤ 1 / 8 := by
    linarith only [previousPhaseBound, budgets.2.2.2.1]
  have recurrence := changed.actual_exit_timing_recurrence frequencyPositive ratioFour nonterminal
    sectionTime origin hit contact incomingTime (coordinate (orbitUnstableShape orbit incomingTime)) actualCoefficient
    (eta / 1000) previousPhaseError (eta / 1000) (eta / 1000) levelPositive coefficientPositive exitIdentity
    errorBudgetPositive.le effectiveSmall passageBound logSmall.le
    (budgets.2.2.2.2.2.2.2 next nextBound) coefficientClose
  have halfTiming : |changed.omega (index.val + 1) * (contact - changed.predictedTime sectionTime count (index.val + 1))| ≤ eta / 2 := by
    apply EulerNonuniqueness.cascade_timing_recurrence_half_bound etaPositive etaSmall ratioFour nextBound previousPhaseBound
      (coefficientError := eta / 1000) (passageError := eta / 1000) (modelError := eta / 1000) le_rfl le_rfl le_rfl
    exact recurrence
  have phaseContact : |changed.omega (index.val + 1) * (contact - hit) - (sectionTime - incomingTime)| ≤ (eta / 100) / 8 :=
    normalizedContact.trans budgets.2.2.2.2.2.1
  obtain ⟨phaseDirection, winding, wrappedPhase⟩ := phaseEstimate prepared path prescribed index nonterminal hit hitInside
    origin contact endpoint endpointPositive (endpointBound.trans endpointPhase) (weakHit index le_rfl) lift
    (fun side => (liftProperties side).1.continuousOn) (fun side => (liftProperties side).2)
    (fun side time inside => liftPolar side time ⟨inside.1, inside.2.trans hitBefore⟩)
    (fun time inside => (targetBounds time ⟨inside.1, inside.2.trans hitBefore⟩).1) exposureHit phaseContact rotation canonical
  let newDirection := rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
  let newPhase := lift 0 hit - orbit.phase incomingTime + orbit.limitingDipoleAngle
  let data : CascadePhysicalStageData prepared path index incomingTime extent historyMagnitude (1 / 16) initialError
      (eta / 100) eta matchingAccuracy := {
    entry := contact
    entryInside := ⟨hitPositive.le.trans contactAfter.le, contactBefore⟩
    firstSeparation := firstSeparation
    direction := newDirection
    directionNorm := directionNorm
    outgoingPhase := newPhase
    directionPhase := phaseDirection.symm
    firstError := firstError
    secondError := secondError
    outgoingProjection := outgoingProjection
    centerUpper := centerUpper
    extents := fun time inside patch => ⟨(contactDomains time inside patch).1, (contactDomains time inside patch).2.1⟩
    domains := fun time inside patch => ⟨(contactDomains time inside patch).2.2.1, (contactDomains time inside patch).2.2.2⟩
    sharp := slowProfile
    winding := winding
    wrappedPhase := wrappedPhase
    timing := halfTiming.trans (by linarith only [etaPositive])
    previousMatch := by
      intro _
      exact ⟨hit, ⟨hitPositive.le, contactAfter.le⟩, rotation, rotationNorm, (matchingClose.trans_le (min_le_right _ _)).le⟩ }
  refine ⟨data, ?_, halfTiming⟩
  change driver.entry < contact
  have originEqual : origin = driver.entry := entryEq drive driveFiner
  rw [← originEqual]
  exact hitAfter.trans contactAfter

end EulerNonuniqueness.Paper
