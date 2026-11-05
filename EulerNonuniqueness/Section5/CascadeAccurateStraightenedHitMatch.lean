import EulerNonuniqueness.Section5.CascadeCompatibleStableAccuracy
import EulerNonuniqueness.Section5.CascadeUniformStraightenedHitIncomingMatch

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_accurate_straightened_hit_match
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (compatible : ∀ᶠ time : ℝ in atBot,
      orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ rootMin ≥ (8 : ℝ),
    ∀ currentStateMagnitude ≥ (0 : ℝ), ∀ currentSharpMagnitude ≥ (0 : ℝ),
    ∃ endpoint > (0 : ℝ), endpoint ≤ 1 ∧
    ∀ᶠ incomingTime : ℝ in atBot, ∀ accuracy > (0 : ℝ),
    ∀ extent magnitudeMax distanceMax coefficient : ℝ,
    1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < coefficient →
    ∃ ratioMin ≥ (2 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    4 * Real.sqrt 2 ≤ coefficient * scales.ratio ^ 2 →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ sectionTime boundaryConstant timingError : ℝ,
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
    (∀ side, Continuous (suppliedLift side) ∧ suppliedLift side 0 = phase (receiver.val + 1)) →
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
    (referenceStraightenedShape motion graph coordinate receiver finish -
      referenceStraightenedShape prepared.reference graph coordinate receiver finish).1 =
        coordinate (orbitUnstableShape orbit incomingTime) →
    let rotation := Complex.exp (Complex.I * ((suppliedLift 0 finish - orbit.phase incomingTime : ℝ) : ℂ))
    halfDiagonalMatchingRotation (positiveHalfDiagonal motion finish receiver) (orbit.positive incomingTime) = rotation ∧
    ‖rotation‖ = 1 ∧
    ‖cascadeNormalizedPointPositions changed motion receiver finish rotation 0 -
      centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ < accuracy := by
  have graphSmooth : ContDiffAt ℝ 2 graph 0 := graphAnalytic.contDiffAt
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, accuracies⟩ :=
    exists_uniform_actual_compatible_stable_accuracy graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative orbit normalized compatible
  obtain ⟨matchingRadius, matchingRadiusPositive, matchings⟩ :=
    exists_uniform_stable_tolerance_actual_straightened_hit_incoming_match graphSmooth coordinateSmooth graphZero
      coordinateZero graphDerivative coordinateDerivative orbit normalized compatible
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨accuracyRadius, accuracyRadiusPositive, accuracyQuarter, rootMin, rootEight, parameters⟩ :=
    accuracies factor factorPositive factorSmall
  let radius := min accuracyRadius (matchingRadius / 2)
  have radiusAccuracy : radius ≤ accuracyRadius := min_le_left _ _
  have radiusMatching : radius < matchingRadius := by
    have bound : radius ≤ matchingRadius / 2 := min_le_right _ _
    linarith only [bound, matchingRadiusPositive]
  refine ⟨radius, lt_min accuracyRadiusPositive (half_pos matchingRadiusPositive),
    radiusAccuracy.trans accuracyQuarter, rootMin, rootEight, ?_⟩
  intro currentStateMagnitude currentStateNonnegative currentSharpMagnitude currentSharpNonnegative
  obtain ⟨endpoint, endpointPositive, endpointOne, precisionFactory⟩ :=
    parameters currentStateMagnitude currentStateNonnegative currentSharpMagnitude currentSharpNonnegative
  refine ⟨endpoint, endpointPositive, endpointOne, ?_⟩
  filter_upwards [matchings] with incomingTime matching
  intro accuracy accuracyPositive
  obtain ⟨stableTolerance, stableTolerancePositive, matchingScales⟩ := matching accuracy accuracyPositive
  have halfPositive : 0 < stableTolerance / 2 := half_pos stableTolerancePositive
  intro extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  obtain ⟨ratioMin, ratioTwo, accuracyScales⟩ := precisionFactory (stableTolerance / 2) halfPositive
    extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  refine ⟨ratioMin, ratioTwo, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower globalGap
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound sectionTime boundaryConstant timingError
    boundaryOne timingNonnegative ratioSeparation
  have ratioBound : 2 ≤ scales.ratio := ratioTwo.trans ratioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  filter_upwards [accuracyScales scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower globalGap
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime
      boundaryConstant timingError boundaryOne timingNonnegative ratioSeparation,
    matchingScales scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) referenceNonnegative]
    with frequency accurate matchAtFrequency
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal entry initialDistance direction
  dsimp only
  intro entries extents magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
    finish finishInside small suppliedLift suppliedProperties suppliedPolar rateBounds currentFullProfile
    currentSharpProfile entryBefore exposure unstableHit
  have stableBound := accurate count phase dipoleAngle prepared path receiver nonterminal entry initialDistance direction
    entries extents magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
    finish finishInside (fun current below time inside => (small current below time inside).trans radiusAccuracy)
    suppliedLift (fun side => (suppliedProperties side).1.continuousOn) (fun side => (suppliedProperties side).2)
    suppliedPolar rateBounds currentFullProfile currentSharpProfile entryBefore exposure
  have stableSmall :
      |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate receiver finish -
        referenceStraightenedShape prepared.reference graph coordinate receiver finish).2| < stableTolerance :=
    stableBound.trans_lt (half_lt_self stableTolerancePositive)
  have radialPrefix : ∀ time ∈ Icc 0 finish,
      |radialShape prepared.trajectory.movingFamily.patchMotion time receiver| ≤ 1 / 2 := by
    intro time inside
    rw [radialShape_eq_unstable_add_stable]
    exact (abs_add _ _).trans ((small receiver le_rfl time inside).trans
      (radiusAccuracy.trans (accuracyQuarter.trans (by norm_num))))
  have alternativeSmall : |unstableShape prepared.trajectory.movingFamily.patchMotion finish receiver| +
      |stableShape prepared.trajectory.movingFamily.patchMotion finish receiver| < matchingRadius :=
    (small receiver le_rfl finish ⟨finishInside.1, le_rfl⟩).trans_lt radiusMatching
  exact matchAtFrequency prepared.toCascadeMaterialPreparedPair path
    (thresholdBound.trans (thresholdEighth.trans (by norm_num))) factorPositive (factorSmall.trans (by norm_num))
    receiver nonterminal finish finishInside radialPrefix alternativeSmall unstableHit stableSmall suppliedLift suppliedProperties suppliedPolar

end EulerNonuniqueness.Paper
