import EulerNonuniqueness.Section5.CascadeGivenMapIncomingWeightedErrorsAtPrecision
import EulerNonuniqueness.Section5.CascadeTimedOlderSourceInputSmall
import EulerNonuniqueness.Section6.SourcePacketActualControlledRetainedSignedWindow
import EulerNonuniqueness.Section5.CascadeAdjacentSourcePhase
import EulerNonuniqueness.Section5.CascadeIncomingDuhamelCoefficient
import EulerNonuniqueness.Section1.SeedFixedLevelHitElapsed

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_coefficient_at_precision
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ rootMin ≥ (8 : ℝ),
    ∀ fullMagnitude sharpMagnitude : ℝ, 0 ≤ fullMagnitude → 0 ≤ sharpMagnitude →
    ∀ tolerance : ℝ, 0 < tolerance →
    let windowTolerance := min ((tolerance / 4) / 2) (1 / 8)
    ∃ coarsePrecision > (0 : ℝ), ∃ endpointMax > (0 : ℝ), endpointMax ≤ 1 ∧
    ∀ endpoint : ℝ, 0 < endpoint → endpoint ≤ endpointMax → ∀ level : ℝ, 0 < level →
    ∀ extent magnitudeMax distanceMax coefficient : ℝ,
    1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < coefficient → coefficient < 1 / 8 →
    ∀ initialError : ℝ, initialError ≤ 1 / 64 →
    ∃ ratioMin ≥ (2 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant timingError : ℝ),
    1 ≤ boundaryConstant → 0 ≤ timingError →
    (coefficient * scales.ratio + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    PrescribedCascadePhases {scales with frequency := frequency} orbit sectionTime count phase dipoleAngle →
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ (receiver : Fin count) (nonterminal : receiver.val + 1 < count), receiver.val + 2 < count →
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, receiver.val < source.val →
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
    (∀ source : Fin count, receiver.val < source.val → ∀ time ∈ Icc 0 (entry source),
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
    (∀ source : Fin count, receiver.val < source.val → 0 ≤ magnitude source ∧
      ∀ time ∈ Icc 0 (entry source), sharpState source time ≤
        magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    (∀ source : Fin count, receiver.val < source.val → magnitude source ≤ magnitudeMax) →
    (∀ source : Fin count, receiver.val < source.val → initialDistance source ≤ distanceMax) →
    (∀ source : Fin count, receiver.val < source.val → ∀ time ∈ Icc 0 (entry source), ∀ patch,
      motion.domain time source patch ⊆ Metric.closedBall (quadrupoleCenter motion time source)
        (extent * changed.length (source.val + 1))) →
    ∀ actualTime : ℕ → ℝ, (∀ source : Fin count, actualTime (source.val + 1) = entry source) →
    |actualTime (receiver.val + 2) - changed.predictedTime sectionTime count (receiver.val + 2)| ≤
      timingError / changed.omega (receiver.val + 2) →
    (∀ source : Fin count, receiver.val < source.val →
      |actualTime (source.val + 1) - changed.predictedTime sectionTime count (source.val + 1)| ≤
        timingError / changed.omega (source.val + 1)) →
    (∀ source : Fin count, receiver.val < source.val → entry source ≤ entry ⟨receiver.val + 1, nonterminal⟩) →
    let drive : Fin count := ⟨receiver.val + 1, nonterminal⟩
    let origin := entry drive
    ∀ outgoingPhase : ℝ, ∀ sourceWinding : ℤ,
    direction drive = Complex.exp (Complex.I * (outgoingPhase : ℂ)) →
    2048 ≤ initialDistance drive →
    20 * initialError + 83200 / (initialDistance drive) ^ 2 ≤ (min (windowTolerance / 4) 1) / 5120 →
    ‖firstDipoleSeparation motion origin drive -
      (changed.length (drive.val + 1) : ℂ) * direction drive‖ ≤ initialError * changed.length (drive.val + 1) →
    ‖secondDipoleSeparation motion origin drive -
      (changed.length (drive.val + 1) : ℂ) * (-direction drive)‖ ≤ initialError * changed.length (drive.val + 1) →
    ∀ hit ∈ Icc 0 path.stop, origin ≤ hit →
    (referenceStraightenedShape motion graph coordinate receiver hit -
      referenceStraightenedShape prepared.reference graph coordinate receiver hit).1 = level →
    (∀ current : Fin count, current.val ≤ receiver.val → ∀ time ∈ Icc 0 hit,
      |unstableShape motion time current| + |stableShape motion time current| ≤ 1 / 4) →
    ∀ suppliedLift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (suppliedLift side) (Icc 0 hit)) →
    (∀ side, suppliedLift side 0 = phase (receiver.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 hit,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
          Complex.exp (Complex.I * (suppliedLift side time : ℂ))) →
    let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    (∀ source : Fin count, receiver.val < source.val → 2 * weight ≤ coefficient * changed.omega (source.val + 1)) →
    let stateBudget := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
    (∀ time ∈ Icc 0 hit, stateBudget time ≤ fullMagnitude * changed.seed (receiver.val + 1) *
      Real.exp (weight * (time - origin))) →
    (∀ time ∈ Icc 0 hit, sharpState receiver time ≤ sharpMagnitude * changed.seed (receiver.val + 1) *
      Real.exp (weight * (time - origin))) →
    ∀ coarseLift : Fin count → Fin 2 → ℝ → ℝ,
    (∀ current : Fin count, current.val < receiver.val → ∀ time ∈ Icc 0 hit,
      prepared.finiteCoordinateSize graph coordinate (coarseLift current) current time +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time current patch ≤ coarsePrecision) →
    changed.seed (receiver.val + 1) * Real.exp (weight * (hit - origin)) ≤ endpoint →
    let residual := 4 * Complex.arg ((changed.location (receiver.val + 1) : ℂ) -
      (changed.location (drive.val + 1) : ℂ)) - 2 * (phase (receiver.val + 1) -
        changed.omega (receiver.val + 1) * origin) - 2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi
    let timingShift := changed.omega (drive.val + 1) *
      (origin - changed.predictedTime sectionTime count (drive.val + 1))
    let phaseError := outgoingPhase - dipoleAngle (drive.val + 1) + timingShift - (sourceWinding : ℝ) * Real.pi
    let actualQ := (referenceStraightenedShape motion graph coordinate receiver hit -
      referenceStraightenedShape prepared.reference graph coordinate receiver hit).1
    let actualCoefficient := Real.exp (-weight * (hit - origin)) * actualQ / changed.seed (receiver.val + 1)
    Real.cos residual = Real.cos (2 * (1 + changed.ratio⁻¹) * timingShift - 2 * phaseError) ∧
    |actualCoefficient - Real.cos residual| ≤ tolerance ∧ 0 < actualCoefficient ∧
      changed.seed (receiver.val + 1) * actualCoefficient * Real.exp (weight * (hit - origin)) = level := by
  classical
  obtain ⟨errorThreshold, errorThresholdPositive, errorEighth, errorCap, errorCapPositive, errorFactors⟩ :=
    exists_uniform_actual_given_map_incoming_weighted_errors_at_precision graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨windowThreshold, windowThresholdPositive, _, windowCap, windowCapPositive, windowFactors⟩ :=
    exists_uniform_actual_controlled_retained_signed_window
  obtain ⟨olderThreshold, olderThresholdPositive, _, olderCap, olderCapPositive, olderFactory⟩ :=
    exists_uniform_actual_timed_older_source_input_small
  obtain ⟨coefficientRadius, coefficientPositive, _, coefficients⟩ :=
    exists_uniform_actual_incoming_duhamel_coefficient graphAnalytic.contDiffAt coordinateSmooth
  let thresholdMax := min errorThreshold (min windowThreshold olderThreshold)
  let rawCap := min errorCap (min windowCap olderCap)
  have thresholdErrors : thresholdMax ≤ errorThreshold := min_le_left _ _
  have thresholdWindow : thresholdMax ≤ windowThreshold := (min_le_right _ _).trans (min_le_left _ _)
  have thresholdOlder : thresholdMax ≤ olderThreshold := (min_le_right _ _).trans (min_le_right _ _)
  have capErrors : rawCap ≤ errorCap := min_le_left _ _
  have capWindow : rawCap ≤ windowCap := (min_le_right _ _).trans (min_le_left _ _)
  have capOlder : rawCap ≤ olderCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨thresholdMax, lt_min errorThresholdPositive (lt_min windowThresholdPositive olderThresholdPositive),
    thresholdErrors.trans errorEighth, rawCap, lt_min errorCapPositive (lt_min windowCapPositive olderCapPositive), ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨errorRoot, errorRootEight, magnitudes⟩ := errorFactors factor factorPositive factorSmall
  obtain ⟨windowRadius, windowRadiusPositive, _, windowRoot, _, windowParameters⟩ :=
    windowFactors factor factorPositive factorSmall
  let physicalRadius := min windowRadius coefficientRadius
  have physicalPositive : 0 < physicalRadius := lt_min windowRadiusPositive coefficientPositive
  obtain ⟨physicalPrecision, physicalPrecisionPositive, refinePhysical⟩ :=
    exists_uniform_actual_full_state_physical_refinement graphAnalytic.contDiffAt coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative physicalPositive
  let rootMin := max errorRoot windowRoot
  refine ⟨rootMin, errorRootEight.trans (le_max_left _ _), ?_⟩
  intro fullMagnitude sharpMagnitude fullNonnegative sharpNonnegative tolerance tolerancePositive
  dsimp only
  let windowTolerance := min ((tolerance / 4) / 2) (1 / 8)
  have windowPositive : 0 < windowTolerance := by dsimp only [windowTolerance]; positivity
  obtain ⟨errorCoarse, errorCoarsePositive, errorEndpoint, errorEndpointPositive, errorEndpointOne, errorParameters⟩ :=
    magnitudes fullMagnitude sharpMagnitude fullNonnegative sharpNonnegative (tolerance / 8) (by positivity)
  let coarsePrecision := min errorCoarse physicalPrecision
  let endpointMax := min errorEndpoint (physicalPrecision / (fullMagnitude + 1))
  have endpointMaxPositive : 0 < endpointMax := by dsimp only [endpointMax]; positivity
  have endpointErrors : endpointMax ≤ errorEndpoint := min_le_left _ _
  have endpointPhysical : endpointMax ≤ physicalPrecision / (fullMagnitude + 1) := min_le_right _ _
  refine ⟨coarsePrecision, lt_min errorCoarsePositive physicalPrecisionPositive, endpointMax,
    endpointMaxPositive, endpointErrors.trans errorEndpointOne, ?_⟩
  intro endpoint endpointPositive endpointBound level levelPositive extent magnitudeMax distanceMax coefficient
    extentOne magnitudeNonnegative distanceNonnegative coefficientPositive coefficientSmall initialError initialErrorSmall
  obtain ⟨errorRatio, errorRatioTwo, errorScales⟩ := errorParameters extent magnitudeMax distanceMax coefficient
    extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  obtain ⟨windowRatio, _, windowScales⟩ := windowParameters extent extentOne coefficient coefficientPositive
    (coefficientSmall.le.trans (by norm_num)) magnitudeMax distanceMax magnitudeNonnegative distanceNonnegative
    (tolerance / 4) (by positivity) initialError initialErrorSmall
  let ratioMin := max errorRatio (max windowRatio (max (24 * distanceMax / windowTolerance) (4 * Real.sqrt 2 / coefficient)))
  refine ⟨ratioMin, errorRatioTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError
    boundaryOne timingNonnegative controlledSeparation
  have errorRatioLarge : errorRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have windowRatioLarge : windowRatio ≤ scales.ratio := (le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge)
  have numericRatio : 24 * distanceMax / windowTolerance ≤ scales.ratio := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge))
  have rateRatio : 4 * Real.sqrt 2 / coefficient ≤ scales.ratio := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge))
  have rateProduct : 4 * Real.sqrt 2 ≤ coefficient * scales.ratio := by
    have bound := (div_le_iff₀ coefficientPositive).mp rateRatio
    simpa only [mul_comm] using bound
  have ratioSeparation : (2 * Real.sqrt 2 + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) := by
    have sqrtNonnegative := Real.sqrt_nonneg (2 : ℝ)
    nlinarith only [rateProduct, controlledSeparation, sqrtNonnegative]
  have ratioBound : 2 ≤ scales.ratio := errorRatioTwo.trans errorRatioLarge
  have olderRate : 4 * Real.sqrt 2 ≤ coefficient * scales.ratio ^ 2 := by
    have sqBound : scales.ratio ≤ scales.ratio ^ 2 := by nlinarith only [ratioBound]
    exact rateProduct.trans (mul_le_mul_of_nonneg_left sqBound coefficientPositive.le)
  have errorRootLarge : errorRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have windowRootLarge : windowRoot ≤ scaleRoot := (le_max_right _ _).trans rootLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (errorRootEight.trans errorRootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := (thresholdBound.trans thresholdErrors).trans errorEighth
  let elapsedMin := max 1 (272 / (3 * tolerance))
  filter_upwards [errorScales scales scaleRoot errorRootLarge amplitudeIdentity errorRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdErrors)
      orbit sectionTime boundaryConstant timingError boundaryOne timingNonnegative ratioSeparation,
    windowScales scales scaleRoot windowRootLarge amplitudeIdentity windowRatioLarge alphaPositive alphaSmall ratioPower
      timingError timingNonnegative controlledSeparation referenceConstant referenceNonnegative referenceAmplitude
      threshold (thresholdBound.trans thresholdWindow) orbit sectionTime boundaryConstant boundaryOne,
    olderFactory sharpMagnitude sharpNonnegative (tolerance / 8) (by positivity) extent extentOne coefficient coefficientPositive
      magnitudeMax distanceMax magnitudeNonnegative distanceNonnegative scales amplitudePositive ratioBound alphaPositive alphaSmall ratioPower
      olderRate timingError timingNonnegative ratioSeparation referenceConstant referenceNonnegative referenceAmplitude
      threshold (thresholdBound.trans thresholdOlder) orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    coefficients scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne
      factorPositive (factorSmall.trans (by norm_num)),
    refinePhysical scales ratioBound alphaPositive referenceConstant referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative
      (by positivity : 0 < physicalRadius / 8),
    scales.eventually_fixed_level_hit_elapsed_gt ratioBound alphaPositive levelPositive fullNonnegative elapsedMin,
    eventually_gt_atTop (0 : ℝ)] with frequency errors window older coefficientEstimate physical referenceSmall elapsed frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared prescribed path receiver nonterminal driveNonterminal
    entry initialDistance direction
  intro entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming
    sourceTiming timeOrder outgoingPhase sourceWinding directionIdentity distanceLarge numericBudget firstInitial secondInitial
    hit hitInside originBefore hitIdentity weakPhysical lift liftContinuous liftInitial liftPolar sourceRates fullProfile sharpProfile
    coarseLift coarseFull exposure
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let drive : Fin count := ⟨receiver.val + 1, nonterminal⟩
  let origin := entry drive
  let growth := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
  let seed := changed.seed (receiver.val + 1)
  have driveFiner : receiver.val < drive.val := by dsimp only [drive]; omega
  have adjacent : receiver.val + 1 = drive.val := rfl
  have driveNonterminal' : drive.val + 1 < count := driveNonterminal
  have originInside : origin ∈ Icc 0 path.stop := ⟨(entries drive driveFiner).1, (entries drive driveFiner).2.1⟩
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  have growthPositive : 0 < growth := by
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (receiver.val + 1)
    dsimp only [growth]; positivity
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time current patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  have sizeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateSize graph coordinate = prepared.finiteCoordinateSize graph coordinate := rfl
  have weighted := errors count phase dipoleAngle (prepared.enlargeCap capErrors) path receiver nonterminal
    entry initialDistance direction entries extents magnitude (by simpa only [rawInvariant, centeredInvariant] using sourceProfiles)
    magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder hit hitInside weakPhysical
    lift liftContinuous liftInitial liftPolar sourceRates
    (by simpa only [rawInvariant, sizeInvariant] using fullProfile)
    (by simpa only [rawInvariant, centeredInvariant] using sharpProfile)
    coarseLift (by
      intro current earlier time inside
      simpa only [rawInvariant, sizeInvariant] using (coarseFull current earlier time inside).trans (min_le_left _ _))
    (exposure.trans (endpointBound.trans endpointErrors))
  dsimp only at weighted
  have remainderSmall := weighted.2.2.1
  have coarseSmall := weighted.2.2.2.2.2.2
  have fullSmall (time : ℝ) (inside : time ∈ Icc 0 hit) :
      prepared.finiteCoordinateSize graph coordinate lift receiver time + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch ≤
        physicalPrecision := by
    have qBound : seed * Real.exp (growth * (time - origin)) ≤ endpoint :=
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 origin) growthPositive.le)) seedPositive.le).trans exposure
    have product := (le_div_iff₀ (by positivity : 0 < fullMagnitude + 1)).mp (endpointBound.trans endpointPhysical)
    have magnitudeBound : fullMagnitude * endpoint ≤ physicalPrecision := by nlinarith only [product, endpointPositive]
    have actual := fullProfile time inside
    change _ ≤ fullMagnitude * seed * Real.exp (growth * (time - origin)) at actual
    exact actual.trans (by
      have scaled := mul_le_mul_of_nonneg_left qBound fullNonnegative
      simpa only [mul_assoc] using scaled.trans magnitudeBound)
  have refined (current : Fin count) (before : current.val ≤ receiver.val) :
      ∀ time ∈ Icc 0 hit, |unstableShape motion time current| + |stableShape motion time current| < physicalRadius := by
    rcases lt_or_eq_of_le before with earlier | equal
    · exact physical prepared path factorPositive current (by omega) hit hitInside (weakPhysical current before)
        (coarseLift current) (fun time inside => (coarseFull current earlier time inside).trans (min_le_right _ _))
    · have same : current = receiver := Fin.ext equal
      subst current
      exact physical prepared path factorPositive receiver nonterminal hit hitInside (weakPhysical receiver le_rfl) lift fullSmall
  have pairedPhysical (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 hit) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver| < physicalRadius := by
    fin_cases side
    · exact refined receiver le_rfl time inside
    · have reference := referenceSmall prepared.toCascadeMaterialPreparedPair time
        ⟨inside.1, inside.2.trans (hitInside.2.trans path.stopBound)⟩ receiver
      have unused := abs_nonneg (diagonalDifference prepared.reference time receiver / changed.length (receiver.val + 1) ^ 2 - 1)
      change |unstableShape prepared.reference time receiver| + |stableShape prepared.reference time receiver| < physicalRadius
      linarith only [reference, unused, physicalPositive]
  have fullDominates : level ≤ prepared.finiteCoordinateSize graph coordinate lift receiver hit +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget hit receiver patch := by
    have identity : (referenceStraightenedShape motion graph coordinate receiver hit).1 -
      (referenceStraightenedShape prepared.reference graph coordinate receiver hit).1 = level := hitIdentity
    have firstBound : level ≤ |(referenceStraightenedShape motion graph coordinate receiver hit).1 -
        (referenceStraightenedShape prepared.reference graph coordinate receiver hit).1| := by
      rw [identity]
      exact le_abs_self level
    have locationPositive := changed.location_pos (receiver.val + 1)
    have lengthPositive := changed.length_pos (receiver.val + 1)
    dsimp only [CascadeSourcePreparedPair.finiteCoordinateSize]
    have extra : 0 ≤ |(referenceStraightenedShape motion graph coordinate receiver hit).2 -
        (referenceStraightenedShape prepared.reference graph coordinate receiver hit).2| +
      |diagonalDifference motion hit receiver - diagonalDifference prepared.reference hit receiver| / changed.length (receiver.val + 1) ^ 2 +
      |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) receiver hit| +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference receiver hit‖ +
      ‖quadrupoleCenter motion hit receiver - quadrupoleCenter prepared.reference hit receiver‖ / changed.location (receiver.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget hit receiver patch := by
      dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    linarith only [firstBound, extra]
  have elapsedLarge : elapsedMin < growth * (hit - origin) := elapsed (receiver.val + 1) (growth * (hit - origin))
    (by
      have actual := fullProfile hit ⟨hitInside.1, le_rfl⟩
      change _ ≤ fullMagnitude * seed * Real.exp (growth * (hit - origin)) at actual
      exact fullDominates.trans actual)
  have exponentialLarge : 68 / tolerance ≤ Real.exp ((3 * growth / 4) * (hit - origin)) := by
    have bound : 272 / (3 * tolerance) ≤ elapsedMin := le_max_right _ _
    have scaled := (div_le_iff₀ (by positivity : 0 < 3 * tolerance)).mp bound
    have linear := Real.add_one_le_exp ((3 * growth / 4) * (hit - origin))
    apply (div_le_iff₀ tolerancePositive).mpr
    have elapsedScaled := mul_le_mul_of_nonneg_right elapsedLarge.le tolerancePositive.le
    nlinarith only [scaled, elapsedScaled, mul_le_mul_of_nonneg_right linear tolerancePositive.le, tolerancePositive]
  have tail : 17 * Real.exp (-(3 * growth / 4) * (hit - origin)) ≤ tolerance / 4 := by
    have reciprocal := one_div_le_one_div_of_le (by positivity : 0 < 68 / tolerance) exponentialLarge
    have same : -(3 * growth / 4) * (hit - origin) = -((3 * growth / 4) * (hit - origin)) := by ring
    rw [same, Real.exp_neg]
    have scaled := mul_le_mul_of_nonneg_left reciprocal (by norm_num : (0 : ℝ) ≤ 17)
    have identity : 17 * (1 / (68 / tolerance)) = tolerance / 4 := by field_simp; ring
    simpa only [one_div] using scaled.trans_eq identity
  have olderEntries (source : Fin count) (later : drive.val < source.val) :
      0 ≤ entry source ∧ entry source ≤ entry drive ∧ 512 ≤ initialDistance source ∧
      initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
      ‖firstDipoleSeparation motion (entry source) source -
        (changed.length (source.val + 1) : ℂ) * direction source‖ ≤ changed.length (source.val + 1) / 64 ∧
      ‖secondDipoleSeparation motion (entry source) source -
        (changed.length (source.val + 1) : ℂ) * (-direction source)‖ ≤ changed.length (source.val + 1) / 64 ∧
      (3 / 4 : ℝ) * changed.length (source.val + 1) * initialDistance source ≤
        (Complex.I * star (direction source) * (firstDipoleCenter motion (entry source) source -
          secondDipoleCenter motion (entry source) source)).re ∧
      ‖firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source‖ ≤
        (5 / 4 : ℝ) * changed.length (source.val + 1) * initialDistance source :=
    ⟨(entries source (by omega)).1, timeOrder source (by omega), (entries source (by omega)).2.2⟩
  have olderEstimates := older count phase dipoleAngle (prepared.enlargeCap capOlder) path receiver nonterminal
    entry initialDistance magnitude direction actualTime timeIdentity originInside nearestTiming
    (fun source later => sourceTiming source (by omega))
    (fun source later => olderEntries source (by simpa only [drive] using later))
    (fun source later => extents source (by omega)) (fun source later => domains source (by omega))
    (fun source later => ⟨(sourceProfiles source (by omega)).1, magnitudeUpper source (by omega)⟩)
    (fun source later => distanceUpper source (by omega))
    (by
      intro source later time inside
      simpa only [rawInvariant, centeredInvariant] using (sourceProfiles source (by omega)).2 time inside)
    hit hitInside (by simpa only [rawInvariant, centeredInvariant] using sharpProfile)
  dsimp only at olderEstimates
  have olderSmall := olderEstimates.2.2.2.2.2.2.2.2
  have windowEstimates := window count phase dipoleAngle (prepared.enlargeCap capWindow) path receiver drive adjacent driveNonterminal'
    entry initialDistance magnitude direction actualTime timeIdentity originInside.1 originInside.2
    (by simpa only [drive, Nat.add_assoc] using nearestTiming)
    (fun source later => sourceTiming source (by omega)) olderEntries
    (fun source later => extents source (by omega)) (fun source later => domains source (by omega))
    (fun time inside => (extents drive driveFiner time inside).1)
    (fun time inside => (extents drive driveFiner time inside).2) (domains drive driveFiner)
    (fun source later => ⟨(sourceProfiles source (by omega)).1, magnitudeUpper source (by omega)⟩)
    (fun source later => distanceUpper source (by omega))
    (by
      intro source later time inside
      simpa only [rawInvariant, centeredInvariant] using (sourceProfiles source (by omega)).2 time inside)
    (by
      intro time inside
      have profile := (sourceProfiles drive driveFiner).2 time inside
      have expPositive := (Real.exp_pos (coefficient * changed.omega (drive.val + 1) * (time - entry drive))).le
      have bound := profile.trans (mul_le_mul_of_nonneg_right (magnitudeUpper drive driveFiner) expPositive)
      simpa only [rawInvariant, centeredInvariant] using bound)
    (by
      intro current before time inside
      exact (refined current (by dsimp only [drive] at before; omega) time
        ⟨inside.1, inside.2.trans originBefore⟩).le.trans (min_le_left _ _))
    outgoingPhase distanceLarge (entries drive driveFiner).2.2.2.1
    (by
      have bound := (div_le_iff₀ windowPositive).mp numericRatio
      have upper := distanceUpper drive driveFiner
      dsimp only
      nlinarith only [bound, upper]) numericBudget
    (by simpa only [← directionIdentity] using firstInitial)
    (by simpa only [← directionIdentity] using secondInitial)
    (by simpa only [← directionIdentity] using (entries drive driveFiner).2.2.2.2.2.2.2.1)
    (entries drive driveFiner).2.2.2.2.2.2.2.2
  dsimp only at windowEstimates
  have hitIdentity' : entry drive + (hit - origin) = hit := by dsimp only [origin]; ring
  have nearest := (windowEstimates.2.2 (hit - origin) (sub_nonneg.mpr originBefore)
    (by rw [hitIdentity']; exact hitInside.2)).2.1
  rw [hitIdentity'] at nearest
  let residual := 4 * Complex.arg ((changed.location (receiver.val + 1) : ℂ) -
    (changed.location (drive.val + 1) : ℂ)) - 2 * (phase (receiver.val + 1) -
      changed.omega (receiver.val + 1) * origin) - 2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi
  have nearestClose : |Real.exp (growth * origin) * (∫ time in (0 : ℝ)..hit, Real.exp (-growth * time) *
      (relativeBlockSourceShapeInput changed motion prepared.reference receiver drive time).1) / seed - Real.cos residual| ≤ tolerance / 2 := by
    change |Real.exp (growth * origin) * (∫ time in (0 : ℝ)..hit, Real.exp (-growth * time) *
      (relativeBlockSourceShapeInput changed motion prepared.reference receiver drive time).1) / seed - Real.cos residual| ≤
        tolerance / 4 + 17 * Real.exp (-(3 * growth / 4) * (hit - origin)) at nearest
    exact nearest.trans (by linarith only [tail])
  have result := coefficientEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver drive adjacent
    hit hitInside.1 hitInside.2 (fun side time inside => (pairedPhysical side time inside).trans_le (min_le_right _ _))
    origin residual level (tolerance / 2) (tolerance / 8) (tolerance / 8) (tolerance / 8) levelPositive hitIdentity nearestClose
    (by
      change Real.exp (growth * origin) * (∫ time in (0 : ℝ)..hit, Real.exp (-growth * time) *
        ‖∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
          relativeBlockSourceShapeInput changed motion prepared.reference receiver source time‖) ≤
            (tolerance / 8) * seed at coarseSmall
      exact coarseSmall)
    (by
      change Real.exp (growth * origin) * (∫ time in (0 : ℝ)..hit, Real.exp (-growth * time) *
        ‖∑ source ∈ Finset.univ.filter (fun source : Fin count => drive.val < source.val),
          relativeBlockSourceShapeInput changed motion prepared.reference receiver source time‖) ≤
            (tolerance / 8) * seed at olderSmall
      exact olderSmall)
    (by
      change Real.exp (growth * origin) * (∫ time in (0 : ℝ)..hit, Real.exp (-growth * time) *
        ‖relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared.toCascadeMaterialPreparedPair)
          graph coordinate receiver time‖) ≤ (tolerance / 8) * seed at remainderSmall
      exact remainderSmall)
  have phaseIdentity := prescribed.adjacent_source_phase_cos_eq ratioPositive.ne' receiver drive adjacent origin outgoingPhase sourceWinding
  dsimp only at phaseIdentity result
  refine ⟨phaseIdentity, result.1.trans ?_, result.2⟩
  linarith only [tolerancePositive]

end EulerNonuniqueness.Paper
