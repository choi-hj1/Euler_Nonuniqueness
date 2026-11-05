import EulerNonuniqueness.Section5.CascadeAvailableIncomingBootstrap
import EulerNonuniqueness.Section5.CascadeGivenMapIncomingWeightedErrorsAtPrecision
import EulerNonuniqueness.Section5.CascadeTimedOlderSourceInputSmall
import EulerNonuniqueness.Section6.SourcePacketActualRetainedPositiveWindow
import EulerNonuniqueness.Section5.CascadeIncomingDuhamelLowerBound
import EulerNonuniqueness.Section5.CascadeUnstableFirstHit

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem positive_hit_profile_dominates {full profile source : ℝ}
    (fullOne : 1 ≤ full) (profileOne : 1 ≤ profile) (sourceOne : 1 ≤ source) :
    profile / 2 ≤ full * (2 * profile + source) := by
  have bound := mul_le_mul_of_nonneg_right fullOne (by linarith : 0 ≤ 2 * profile + source)
  linarith only [bound, profileOne, sourceOne]

theorem exists_uniform_actual_positive_first_hit :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ),
      ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ currentMagnitude ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ), ∃ endpointMax > (0 : ℝ),
      endpointMax ≤ 1 ∧ ∀ endpoint : ℝ, 0 < endpoint → endpoint ≤ endpointMax →
      ∀ level : ℝ, 0 < level → level ≤ endpoint / 2 →
      ∀ precision : ℝ, 0 < precision →
      ∀ extent magnitudeMax distanceMax sourceRate : ℝ,
      1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < sourceRate → sourceRate < 1 / 8 →
      ∀ initialError : ℝ, initialError ≤ 1 / 64 → ∀ phaseTolerance : ℝ, 0 ≤ phaseTolerance →
      ∃ ratioMin ≥ (2 : ℝ),
      ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
      ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
      ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
      ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant timingError : ℝ),
      1 ≤ boundaryConstant → 0 ≤ timingError → 0 < sectionTime →
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
          referenceStraightenedShape prepared.reference graph coordinate index hit).1 = level ∧
        ∀ time : ℝ, 0 ≤ time → time < hit →
          (referenceStraightenedShape motion graph coordinate index time -
            referenceStraightenedShape prepared.reference graph coordinate index time).1 < level) ∧
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
    coordinateDerivative, chartConstant, chartOne, incomingThreshold, incomingThresholdPositive, incomingEighth,
    compatible, incomingCap, incomingCapPositive, incomingFactors⟩ := exists_uniform_actual_available_incoming_bootstrap
  obtain ⟨errorThreshold, errorThresholdPositive, _, errorCap, errorCapPositive, errorFactors⟩ :=
    exists_uniform_actual_given_map_incoming_weighted_errors_at_precision graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨windowThreshold, windowThresholdPositive, _, windowCap, windowCapPositive, windowFactors⟩ :=
    exists_uniform_actual_controlled_retained_positive_window
  obtain ⟨olderThreshold, olderThresholdPositive, _, olderCap, olderCapPositive, olderFactory⟩ :=
    exists_uniform_actual_timed_older_source_input_small
  obtain ⟨duhamelRadius, duhamelPositive, _, duhamel⟩ :=
    exists_uniform_actual_incoming_duhamel_lower_bound graphAnalytic.contDiffAt coordinateSmooth
  obtain ⟨hitRadius, hitPositive, _, firstHit⟩ :=
    exists_uniform_actual_unstable_first_hit graphAnalytic.contDiffAt coordinateSmooth
  let thresholdMax := min incomingThreshold (min errorThreshold (min windowThreshold olderThreshold))
  let rawCap := min incomingCap (min errorCap (min windowCap olderCap))
  have thresholdPositive : 0 < thresholdMax := by dsimp only [thresholdMax]; positivity
  have thresholdIncoming : thresholdMax ≤ incomingThreshold := min_le_left _ _
  have thresholdErrors : thresholdMax ≤ errorThreshold := (min_le_right _ _).trans (min_le_left _ _)
  have thresholdWindow : thresholdMax ≤ windowThreshold := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have thresholdOlder : thresholdMax ≤ olderThreshold := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have capIncoming : rawCap ≤ incomingCap := min_le_left _ _
  have capErrors : rawCap ≤ errorCap := (min_le_right _ _).trans (min_le_left _ _)
  have capWindow : rawCap ≤ windowCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have capOlder : rawCap ≤ olderCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have capPositive : 0 < rawCap := by dsimp only [rawCap]; positivity
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive,
    thresholdIncoming.trans incomingEighth, compatible, rawCap, capPositive, ?_⟩
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
  have profileOne' : 1 ≤ profileMagnitude := profileMagnitudeOne
  have currentOne : 1 ≤ currentMagnitude := by
    apply one_le_mul_of_one_le_of_one_le fullProfileOne
    linarith only [profileOne', sourceOne]
  have currentNonnegative : 0 ≤ currentMagnitude := zero_le_one.trans currentOne
  have profileCurrent : profileMagnitude / 2 ≤ currentMagnitude := by
    exact positive_hit_profile_dominates fullProfileOne profileOne' sourceOne
  obtain ⟨errorRoot, errorRootEight, errorMagnitudes⟩ := errorFactors factor factorPositive factorSmall
  obtain ⟨coarsePrecision, coarsePrecisionPositive, errorEndpoint, errorEndpointPositive, _, errorParameters⟩ :=
    errorMagnitudes currentMagnitude currentMagnitude currentNonnegative currentNonnegative (1 / 16) (by norm_num)
  obtain ⟨windowRadius, windowRadiusPositive, _, windowRoot, windowRootEight, windowParameters⟩ :=
    windowFactors factor factorPositive factorSmall
  let physicalRadius := min windowRadius (min duhamelRadius hitRadius)
  have physicalPositive : 0 < physicalRadius := lt_min windowRadiusPositive (lt_min duhamelPositive hitPositive)
  obtain ⟨physicalPrecision, physicalPrecisionPositive, refinePhysical⟩ :=
    exists_uniform_actual_full_state_physical_refinement graphAnalytic.contDiffAt coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative physicalPositive
  let rootMin := max incomingRoot (max errorRoot windowRoot)
  let endpointMax := min incomingEndpoint (min errorEndpoint (physicalPrecision / (currentMagnitude + 1)))
  have endpointMaxPositive : 0 < endpointMax := by dsimp only [endpointMax]; positivity
  have endpointMaxIncoming : endpointMax ≤ incomingEndpoint := min_le_left _ _
  have endpointMaxErrors : endpointMax ≤ errorEndpoint := (min_le_right _ _).trans (min_le_left _ _)
  have endpointMaxPhysical : endpointMax ≤ physicalPrecision / (currentMagnitude + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨currentMagnitude, currentOne, rootMin, incomingRootEight.trans (le_max_left _ _),
    endpointMax, endpointMaxPositive, endpointMaxIncoming.trans incomingEndpointOne, ?_⟩
  intro endpoint endpointPositive endpointBound level levelPositive levelBound precision precisionPositive
    extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive sourceRateSmall
    initialError initialErrorSmall phaseTolerance phaseNonnegative
  let selectedPrecision := min precision (min coarsePrecision physicalPrecision)
  have selectedPositive : 0 < selectedPrecision := lt_min precisionPositive (lt_min coarsePrecisionPositive physicalPrecisionPositive)
  obtain ⟨incomingRatio, incomingRatioTwo, incomingScales⟩ :=
    incomingParameters endpoint endpointPositive (endpointBound.trans endpointMaxIncoming) selectedPrecision selectedPositive
      extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive sourceRateSmall
  obtain ⟨errorRatio, _, errorScales⟩ := errorParameters extent magnitudeMax distanceMax sourceRate extentOne
    magnitudeNonnegative distanceNonnegative sourceRatePositive
  obtain ⟨windowRatio, _, windowScales⟩ := windowParameters extent extentOne sourceRate sourceRatePositive
    (sourceRateSmall.le.trans (by norm_num)) magnitudeMax distanceMax magnitudeNonnegative distanceNonnegative
    initialError initialErrorSmall phaseTolerance phaseNonnegative
  let ratioMin := max incomingRatio (max errorRatio (max windowRatio (max (768 * distanceMax) (4 * Real.sqrt 2 / sourceRate))))
  refine ⟨ratioMin, incomingRatioTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError
    boundaryOne timingNonnegative sectionPositive phaseBudget controlledSeparation
  have incomingRatioLarge : incomingRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have errorRatioLarge : errorRatio ≤ scales.ratio := (le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge)
  have windowRatioLarge : windowRatio ≤ scales.ratio := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge))
  have numericRatio : 768 * distanceMax ≤ scales.ratio := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge)))
  have rateRatio : 4 * Real.sqrt 2 / sourceRate ≤ scales.ratio := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge)))
  have ratioBound : 2 ≤ scales.ratio := incomingRatioTwo.trans incomingRatioLarge
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  have rateProduct : 4 * Real.sqrt 2 ≤ sourceRate * scales.ratio := by
    have bound := (div_le_iff₀ sourceRatePositive).mp rateRatio
    simpa only [mul_comm] using bound
  have ratioSeparation : (2 * Real.sqrt 2 + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) := by
    have sqrtNonnegative := Real.sqrt_nonneg (2 : ℝ)
    nlinarith only [rateProduct, controlledSeparation, sqrtNonnegative]
  have olderRate : 4 * Real.sqrt 2 ≤ sourceRate * scales.ratio ^ 2 := by
    have sqBound : scales.ratio ≤ scales.ratio ^ 2 := by nlinarith only [ratioBound]
    exact rateProduct.trans (mul_le_mul_of_nonneg_left sqBound sourceRatePositive.le)
  have incomingRootLarge : incomingRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have errorRootLarge : errorRoot ≤ scaleRoot := (le_max_left _ _).trans ((le_max_right _ _).trans rootLarge)
  have windowRootLarge : windowRoot ≤ scaleRoot := (le_max_right _ _).trans ((le_max_right _ _).trans rootLarge)
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (incomingRootEight.trans incomingRootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := (thresholdBound.trans thresholdIncoming).trans incomingEighth
  filter_upwards [incomingScales scales scaleRoot incomingRootLarge amplitudeIdentity incomingRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdIncoming)
      orbit sectionTime boundaryConstant timingError boundaryOne timingNonnegative sectionPositive ratioSeparation,
    errorScales scales scaleRoot errorRootLarge amplitudeIdentity errorRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdErrors)
      orbit sectionTime boundaryConstant timingError boundaryOne timingNonnegative ratioSeparation,
    windowScales scales scaleRoot windowRootLarge amplitudeIdentity windowRatioLarge alphaPositive alphaSmall ratioPower
      timingError timingNonnegative phaseBudget controlledSeparation referenceConstant referenceNonnegative referenceAmplitude
      threshold (thresholdBound.trans thresholdWindow) orbit sectionTime boundaryConstant boundaryOne,
    olderFactory currentMagnitude currentNonnegative (1 / 16) (by norm_num) extent extentOne sourceRate sourceRatePositive
      magnitudeMax distanceMax magnitudeNonnegative distanceNonnegative scales amplitudePositive ratioBound alphaPositive alphaSmall ratioPower
      olderRate timingError timingNonnegative ratioSeparation referenceConstant referenceNonnegative referenceAmplitude
      threshold (thresholdBound.trans thresholdOlder) orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    duhamel scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne
      factorPositive (factorSmall.trans (by norm_num)),
    refinePhysical scales ratioBound alphaPositive referenceConstant referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative
      (by positivity : 0 < physicalRadius / 8),
    scales.eventually_polynomial_seed_rpow_lt ratioBound alphaPositive 0 (by norm_num : (0 : ℝ) < 1)
      (by positivity : 0 < level / (currentMagnitude + 1)), eventually_gt_atTop (0 : ℝ)]
    with frequency incoming errors window older lowerBound physical referenceSmall seedSmall frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path prescribed index nonterminal driveNonterminal
    entry initialDistance direction
  dsimp only
  intro entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming
    sourceTiming timeOrder originBound sourceRates outgoingPhase sourceWinding directionIdentity phaseSmall distanceLarge
    numericBudget firstInitial secondInitial
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let drive : Fin count := ⟨index.val + 1, nonterminal⟩
  let origin := entry drive
  let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  let finish := origin + Real.log (endpoint / changed.seed (index.val + 1)) / growth
  have driveFiner : index.val < drive.val := by dsimp only [drive]; omega
  have adjacent : index.val + 1 = drive.val := rfl
  have driveNonterminal' : drive.val + 1 < count := driveNonterminal
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time current patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  have sizeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateSize graph coordinate = prepared.finiteCoordinateSize graph coordinate := rfl
  have payload := incoming count phase dipoleAngle (prepared.enlargeCap capIncoming) path index nonterminal
    entry initialDistance direction entries extents magnitude (by simpa only [rawInvariant, centeredInvariant] using sourceProfiles)
    magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder originBound sourceRates
  dsimp only at payload
  simp only [rawInvariant, centeredInvariant, sizeInvariant] at payload
  obtain ⟨finishPositive, elapsedPositive, elapsedSmall, elapsedLarge, exposure, finishSmall, finishAvailable,
    coarserPhysical, targetData, coarseLift, coarseLiftProperties, coarseLiftPolar, coarseFull⟩ := payload
  obtain ⟨targetRadial, targetPhysical, lift, liftProperties, liftPolar,
    shapeContinuous, shapeZero, shapeProfile, stateContinuous, stateZero, stateI, forcingI, targetBounds⟩ := targetData
  have finishInside : finish ∈ Icc 0 path.stop := ⟨finishPositive.le, finishAvailable⟩
  have originInside : origin ∈ Icc 0 path.stop := ⟨(entries drive driveFiner).1, (entries drive driveFiner).2.1⟩
  have originBefore : origin < finish := by
    have elapsedPositive' : 0 < finish - origin := elapsedPositive
    linarith only [elapsedPositive']
  have ratioPositive' : 0 < changed.ratio := ratioPositive
  have seedPositive : 0 < changed.seed (index.val + 1) := changed.seed_pos frequencyPositive ratioPositive' _
  have growthPositive : 0 < growth := by
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive' (index.val + 1)
    dsimp only [growth]; positivity
  have weakPhysical (current : Fin count) (before : current.val ≤ index.val) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape motion time current| + |stableShape motion time current| ≤ 1 / 4 := by
    rcases lt_or_eq_of_le before with earlier | equal
    · exact ((coarserPhysical time inside current earlier).1.le).trans (by linarith only [radiusQuarter])
    · have same : current = index := Fin.ext equal
      subst current
      exact (targetPhysical time inside).le.trans (by linarith only [targetRadiusQuarter])
  have currentProfile := fun time inside => (targetBounds time inside).1
  have sharpProfile := fun time inside => (targetBounds time inside).2
  have weighted := errors count phase dipoleAngle (prepared.enlargeCap capErrors) path index nonterminal
    entry initialDistance direction entries extents magnitude (by simpa only [rawInvariant, centeredInvariant] using sourceProfiles)
    magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder finish finishInside
    (fun current before time inside => weakPhysical current before time inside) lift
    (fun side => (liftProperties side).1.continuousOn) (fun side => (liftProperties side).2) liftPolar sourceRates
    (by simpa only [rawInvariant, sizeInvariant] using currentProfile)
    (by simpa only [rawInvariant, centeredInvariant] using sharpProfile)
    coarseLift (by
      intro current earlier time inside
      simpa only [rawInvariant, sizeInvariant] using
        (coarseFull time inside current earlier).trans ((min_le_right precision _).trans (min_le_left _ _)))
    (exposure.le.trans (endpointBound.trans endpointMaxErrors))
  dsimp only at weighted
  have remainderSmall := weighted.2.2.1
  have coarseSmall := weighted.2.2.2.2.2.2
  have qBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) ≤ endpoint := by
    rw [← exposure]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 origin) growthPositive.le)) seedPositive.le
  have magnitudeBound : currentMagnitude * endpoint ≤ physicalPrecision := by
    have scaled := mul_le_mul_of_nonneg_left (endpointBound.trans endpointMaxPhysical)
      (show 0 ≤ currentMagnitude + 1 by positivity)
    have identity : (currentMagnitude + 1) * (physicalPrecision / (currentMagnitude + 1)) = physicalPrecision := by field_simp
    rw [identity] at scaled
    nlinarith only [scaled, endpointPositive]
  have refined (current : Fin count) (before : current.val ≤ index.val) :
      ∀ time ∈ Icc 0 finish, |unstableShape motion time current| + |stableShape motion time current| < physicalRadius := by
    rcases lt_or_eq_of_le before with earlier | equal
    · exact physical prepared path factorPositive current (by omega) finish finishInside
        (fun time inside => weakPhysical current (Nat.le_of_lt earlier) time inside) (coarseLift current) (by
          intro time inside
          exact (coarseFull time inside current earlier).trans ((min_le_right precision _).trans (min_le_right _ _)))
    · have same : current = index := Fin.ext equal
      subst current
      apply physical prepared path factorPositive index nonterminal finish finishInside
        (fun time inside => weakPhysical index le_rfl time inside) lift
      intro time inside
      calc
        _ ≤ currentMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) := currentProfile time inside
        _ = currentMagnitude * (changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) := by ring
        _ ≤ currentMagnitude * endpoint := mul_le_mul_of_nonneg_left (qBound time inside) currentNonnegative
        _ ≤ physicalPrecision := magnitudeBound
  have pairedPhysical (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| < physicalRadius := by
    fin_cases side
    · exact refined index le_rfl time inside
    · have reference := referenceSmall prepared.toCascadeMaterialPreparedPair time
        ⟨inside.1, inside.2.trans (finishAvailable.trans path.stopBound)⟩ index
      have unused := abs_nonneg (diagonalDifference prepared.reference time index / changed.length (index.val + 1) ^ 2 - 1)
      change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < physicalRadius
      linarith only [reference, unused, physicalPositive]
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
  have olderEstimates := older count phase dipoleAngle (prepared.enlargeCap capOlder) path index nonterminal
    entry initialDistance magnitude direction actualTime timeIdentity originInside nearestTiming
    (fun source later => sourceTiming source (by omega))
    (fun source later => olderEntries source (by simpa only [drive] using later))
    (fun source later => extents source (by omega)) (fun source later => domains source (by omega))
    (fun source later => ⟨(sourceProfiles source (by omega)).1, magnitudeUpper source (by omega)⟩)
    (fun source later => distanceUpper source (by omega))
    (by
      intro source later time inside
      simpa only [rawInvariant, centeredInvariant] using (sourceProfiles source (by omega)).2 time inside)
    finish finishInside (by simpa only [rawInvariant, centeredInvariant] using sharpProfile)
  dsimp only at olderEstimates
  have olderSmall := olderEstimates.2.2.2.2.2.2.2.2
  have windowEstimates := window count phase dipoleAngle (prepared.enlargeCap capWindow) prescribed path index drive adjacent driveNonterminal'
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
      have expPositive := (Real.exp_pos (sourceRate * changed.omega (drive.val + 1) * (time - entry drive))).le
      have bound := profile.trans (mul_le_mul_of_nonneg_right (magnitudeUpper drive driveFiner) expPositive)
      simpa only [rawInvariant, centeredInvariant] using bound)
    (by
      intro current before time inside
      exact (refined current (by dsimp only [drive] at before; omega) time
        ⟨inside.1, inside.2.trans originBefore.le⟩).le.trans (min_le_left _ _))
    outgoingPhase sourceWinding phaseSmall distanceLarge (entries drive driveFiner).2.2.2.1
    (by have upper := distanceUpper drive driveFiner; dsimp only; nlinarith only [numericRatio, upper]) numericBudget
    (by simpa only [← directionIdentity] using firstInitial)
    (by simpa only [← directionIdentity] using secondInitial)
    (by simpa only [← directionIdentity] using (entries drive driveFiner).2.2.2.2.2.2.2.1)
    (entries drive driveFiner).2.2.2.2.2.2.2.2
  dsimp only at windowEstimates
  have finishIdentity : entry drive + (finish - origin) = finish := by dsimp only [origin]; ring
  have nearestLower := (windowEstimates.2.2.2 (finish - origin) elapsedPositive.le
    (by rw [finishIdentity]; exact finishAvailable) elapsedLarge).2
  rw [finishIdentity] at nearestLower
  change (3 / 4 : ℝ) ≤ Real.exp (growth * origin) *
    (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) *
      (relativeBlockSourceShapeInput changed motion prepared.reference index drive time).1) /
        changed.seed (index.val + 1) at nearestLower
  have nearestBound : 3 * changed.seed (index.val + 1) / 4 ≤ Real.exp (growth * origin) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) *
        (relativeBlockSourceShapeInput changed motion prepared.reference index drive time).1) := by
    have scaled := (le_div_iff₀ seedPositive).mp nearestLower
    convert scaled using 1; ring
  have actualLower := lowerBound count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index drive adjacent
    finish finishPositive.le finishAvailable
    (fun side time inside => (pairedPhysical side time inside).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    origin nearestBound (by
      change Real.exp (growth * origin) * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) *
        ‖∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < index.val),
          relativeBlockSourceShapeInput changed motion prepared.reference index source time‖) ≤
            (1 / 16 : ℝ) * changed.seed (index.val + 1) at coarseSmall
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using coarseSmall)
    (by
      change Real.exp (growth * origin) * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) *
        ‖∑ source ∈ Finset.univ.filter (fun source : Fin count => drive.val < source.val),
          relativeBlockSourceShapeInput changed motion prepared.reference index source time‖) ≤
            (1 / 16 : ℝ) * changed.seed (index.val + 1) at olderSmall
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using olderSmall)
    (by
      change Real.exp (growth * origin) * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) *
        ‖relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared.toCascadeMaterialPreparedPair)
          graph coordinate index time‖) ≤ (1 / 16 : ℝ) * changed.seed (index.val + 1) at remainderSmall
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using remainderSmall)
  have unstableLower : endpoint / 2 ≤ (referenceStraightenedShape motion graph coordinate index finish -
      referenceStraightenedShape prepared.reference graph coordinate index finish).1 := by
    rw [exposure] at actualLower
    exact actualLower
  obtain ⟨hit, hitPositive, hitBefore, hitIdentity, leastHit⟩ :=
    firstHit prepared.toCascadeMaterialPreparedPair path index nonterminal finish finishPositive.le finishAvailable
      (fun side time inside => (pairedPhysical side time inside).trans_le ((min_le_right _ _).trans (min_le_right _ _)))
      level levelPositive (levelBound.trans unstableLower)
  have seedBound : currentMagnitude * changed.seed (index.val + 1) < level := by
    have small := seedSmall (index.val + 1)
    simp only [pow_zero, Real.rpow_one, one_mul] at small
    have scaled := (lt_div_iff₀ (show 0 < currentMagnitude + 1 by positivity)).mp small
    nlinarith only [scaled, seedPositive]
  have hitAfter : origin < hit := by
    by_contra! beforeOrigin
    have exponentBound : Real.exp (growth * (hit - origin)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos growthPositive.le (sub_nonpos.mpr beforeOrigin))
    have profile := (shapeProfile hit ⟨hitPositive.le, hitBefore⟩).2
    have qNonnegative : 0 ≤ changed.seed (index.val + 1) * Real.exp (growth * (hit - origin)) := by positivity
    have shapeBound :
        |(referenceStraightenedShape motion graph coordinate index hit).1 -
          (referenceStraightenedShape prepared.reference graph coordinate index hit).1| +
        |(referenceStraightenedShape motion graph coordinate index hit).2 -
          (referenceStraightenedShape prepared.reference graph coordinate index hit).2| < level := by
      calc
        _ ≤ (profileMagnitude / 2) * changed.seed (index.val + 1) * Real.exp (growth * (hit - origin)) := profile
        _ ≤ currentMagnitude * (changed.seed (index.val + 1) * Real.exp (growth * (hit - origin))) := by
          nlinarith only [mul_le_mul_of_nonneg_right profileCurrent qNonnegative]
        _ ≤ currentMagnitude * changed.seed (index.val + 1) := by
          have bound := mul_le_mul_of_nonneg_left exponentBound (mul_nonneg currentNonnegative seedPositive.le)
          simpa only [mul_one, mul_assoc] using bound
        _ < level := seedBound
    have identity : (referenceStraightenedShape motion graph coordinate index hit).1 -
        (referenceStraightenedShape prepared.reference graph coordinate index hit).1 = level := hitIdentity
    rw [identity] at shapeBound
    linarith only [shapeBound, le_abs_self level,
      abs_nonneg ((referenceStraightenedShape motion graph coordinate index hit).2 -
        (referenceStraightenedShape prepared.reference graph coordinate index hit).2)]
  refine ⟨finishPositive, elapsedPositive, elapsedSmall, elapsedLarge, exposure, finishSmall, finishAvailable,
    unstableLower, ⟨hit, hitAfter, hitBefore, hitIdentity, leastHit⟩,
    (fun time inside current before => weakPhysical current before time inside),
    ⟨lift, liftProperties, liftPolar, stateContinuous, stateZero, stateI, forcingI, targetBounds⟩,
    coarseLift, coarseLiftProperties, coarseLiftPolar, ?_⟩
  intro time inside current earlier
  exact (coarseFull time inside current earlier).trans (min_le_left precision _)

end EulerNonuniqueness.Paper
