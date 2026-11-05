import EulerNonuniqueness.Section5.CascadeCompatibleStableHistory
import EulerNonuniqueness.Section5.CascadeLeadingStableSmall

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_compatible_stable_accuracy
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0)
    (certificateOrbit : SeparatingOrbit) (certificateNormalized : IsNormalizedSeparatingOrbit certificateOrbit)
    (certificateCompatible : ∀ᶠ time : ℝ in atBot,
      orbitStableShape certificateOrbit time = graph (orbitUnstableShape certificateOrbit time)) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ rootMin ≥ (8 : ℝ),
    ∀ currentStateMagnitude ≥ (0 : ℝ), ∀ currentSharpMagnitude ≥ (0 : ℝ),
    ∃ endpoint > (0 : ℝ), endpoint ≤ 1 ∧
    ∀ precision > (0 : ℝ),
    ∀ extent magnitudeMax distanceMax coefficient : ℝ,
    1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < coefficient →
    ∃ ratioMin ≥ (2 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    4 * Real.sqrt 2 ≤ coefficient * scales.ratio ^ 2 →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant timingError : ℝ),
    1 ≤ boundaryConstant → 0 ≤ timingError →
    (2 * Real.sqrt 2 + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ (receiver : Fin count) (nonterminal : receiver.val + 1 < count),
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
    ∀ finish ∈ Icc 0 path.stop,
    (∀ current : Fin count, current.val ≤ receiver.val → ∀ time ∈ Icc 0 finish,
      |unstableShape motion time current| + |stableShape motion time current| ≤ radius) →
    ∀ suppliedLift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (suppliedLift side) (Icc 0 finish)) →
    (∀ side, suppliedLift side 0 = phase (receiver.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
          Complex.exp (Complex.I * (suppliedLift side time : ℂ))) →
    let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    (∀ source : Fin count, receiver.val < source.val → 2 * weight ≤ coefficient * changed.omega (source.val + 1)) →
    let stateBudget := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
    let origin := entry ⟨receiver.val + 1, nonterminal⟩
    (∀ time ∈ Icc 0 finish, stateBudget time ≤ currentStateMagnitude * changed.seed (receiver.val + 1) *
      Real.exp (weight * (time - origin))) →
    (∀ time ∈ Icc 0 finish, sharpState receiver time ≤ currentSharpMagnitude * changed.seed (receiver.val + 1) *
      Real.exp (weight * (time - origin))) →
    origin ≤ finish →
    changed.seed (receiver.val + 1) * Real.exp (weight * (finish - origin)) ≤ endpoint →
    |(referenceStraightenedShape motion graph coordinate receiver finish -
      referenceStraightenedShape prepared.reference graph coordinate receiver finish).2| ≤ precision := by
  obtain ⟨chartConstant, chartOne, pointConstant, pointOne, historyThreshold, historyThresholdPositive,
    historyEighth, historyCap, historyCapPositive, histories⟩ :=
    exists_uniform_actual_compatible_stable_history graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative certificateOrbit certificateNormalized certificateCompatible
  obtain ⟨leadingThreshold, leadingThresholdPositive, leadingEighth, leadingCap, leadingCapPositive, leadings⟩ :=
    exists_uniform_actual_leading_stable_small
  let thresholdMax := min historyThreshold leadingThreshold
  let rawCap := min historyCap leadingCap
  have historyCapBound : rawCap ≤ historyCap := min_le_left _ _
  have leadingCapBound : rawCap ≤ leadingCap := min_le_right _ _
  refine ⟨thresholdMax, lt_min historyThresholdPositive leadingThresholdPositive,
    (min_le_left _ _).trans historyEighth, rawCap, lt_min historyCapPositive leadingCapPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨historyRadius, historyRadiusPositive, historyQuarter, historyRoot, historyRootEight,
    stableConstant, stableOne, historyParameters⟩ := histories factor factorPositive factorSmall
  obtain ⟨leadingRadius, leadingRadiusPositive, leadingQuarter, leadingRoot, leadingRootEight, leadingParameters⟩ :=
    leadings factorPositive factorSmall
  let radius := min historyRadius leadingRadius
  let rootMin := max historyRoot leadingRoot
  refine ⟨radius, lt_min historyRadiusPositive leadingRadiusPositive, (min_le_left _ _).trans historyQuarter,
    rootMin, historyRootEight.trans (le_max_left _ _), ?_⟩
  intro currentStateMagnitude currentStateNonnegative currentSharpMagnitude currentSharpNonnegative
  obtain ⟨endpoint, endpointPositive, endpointOne, _, historyPrecision⟩ :=
    historyParameters currentStateMagnitude currentStateNonnegative
  refine ⟨endpoint, endpointPositive, endpointOne, ?_⟩
  intro precision precisionPositive
  have halfPositive : 0 < precision / 2 := half_pos precisionPositive
  obtain ⟨tolerance, tolerancePositive, toleranceOne, historyData⟩ := historyPrecision (precision / 2) halfPositive
  intro extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  obtain ⟨historyRatio, historyRatioTwo, historyScales⟩ := historyData extent magnitudeMax distanceMax coefficient
    extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  obtain ⟨leadingRatio, leadingRatioTwo, leadingScales⟩ := leadingParameters currentSharpMagnitude currentSharpNonnegative
    (precision / 2) halfPositive extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative
    distanceNonnegative coefficientPositive
  let ratioMin := max historyRatio leadingRatio
  refine ⟨ratioMin, historyRatioTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower globalGap
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime
    boundaryConstant timingError boundaryOne timingNonnegative ratioSeparation
  have historyRootBound : historyRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have leadingRootBound : leadingRoot ≤ scaleRoot := (le_max_right _ _).trans rootLarge
  have historyRatioBound : historyRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have leadingRatioBound : leadingRatio ≤ scales.ratio := (le_max_right _ _).trans ratioLarge
  have historyThresholdBound : threshold ≤ historyThreshold := thresholdBound.trans (min_le_left _ _)
  have leadingThresholdBound : threshold ≤ leadingThreshold := thresholdBound.trans (min_le_right _ _)
  filter_upwards [historyScales scales scaleRoot historyRootBound amplitudeIdentity historyRatioBound alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold historyThresholdBound orbit sectionTime
      boundaryConstant timingError boundaryOne timingNonnegative ratioSeparation,
    leadingScales scales scaleRoot leadingRootBound amplitudeIdentity leadingRatioBound alphaPositive alphaSmall ratioPower globalGap
      referenceConstant referenceNonnegative referenceAmplitude threshold leadingThresholdBound orbit sectionTime
      boundaryConstant timingError boundaryOne timingNonnegative ratioSeparation]
    with frequency historyEstimate leadingEstimate
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal entry initialDistance direction
  dsimp only
  intro entries extents magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
    finish finishInside small suppliedLift suppliedContinuous suppliedInitial suppliedPolar rateBounds currentFullProfile
    currentSharpProfile entryBefore exposure
  have rawInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centerInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have sizeInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).finiteCoordinateSize = prepared.finiteCoordinateSize := rfl
  have historyProfiles := profiles
  rw [← rawInvariant historyCapBound, ← centerInvariant historyCapBound] at historyProfiles
  have historyCurrent := currentFullProfile
  rw [← rawInvariant historyCapBound, ← sizeInvariant historyCapBound] at historyCurrent
  have history := historyEstimate count phase dipoleAngle (prepared.enlargeCap historyCapBound) path receiver nonterminal
    entry initialDistance direction entries extents magnitude historyProfiles magnitudeUpper distanceUpper domains actualTime
    timeIdentity nearestTiming sourceTiming timeOrder finish finishInside
    (fun current below time inside => (small current below time inside).trans (min_le_left _ _))
    suppliedLift suppliedContinuous suppliedInitial suppliedPolar rateBounds historyCurrent exposure
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, accuracy⟩ := history
  have leadingProfiles := profiles
  have leadingCurrent := currentSharpProfile
  rw [← rawInvariant leadingCapBound, ← centerInvariant leadingCapBound] at leadingProfiles leadingCurrent
  have leading := leadingEstimate count phase dipoleAngle (prepared.enlargeCap leadingCapBound) path receiver nonterminal
    entry initialDistance direction entries extents magnitude leadingProfiles magnitudeUpper distanceUpper domains actualTime
    timeIdentity nearestTiming sourceTiming timeOrder finish finishInside
    (fun current below time inside => (small current below.le time inside).trans (min_le_right _ _))
    rateBounds leadingCurrent entryBefore (exposure.trans endpointOne)
  have stable := accuracy finish ⟨finishInside.1, le_rfl⟩
  have leadingSmall := leading.2.2
  with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at stable leadingSmall
  exact stable.trans (by linarith only [leadingSmall])

end EulerNonuniqueness.Paper
