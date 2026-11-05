import EulerNonuniqueness.Section5.CascadeGivenMapAdditiveWeightedClosure
import EulerNonuniqueness.Section5.CascadeCalibratedKnownSourceBudgetFromDomains
import EulerNonuniqueness.Section5.CascadePhaseLiftCoherence

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_domain_additive_weighted_closure_factor_uniform
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ coarseConstant ≥ (0 : ℝ), ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∃ commonIncoming ≥ (0 : ℝ), ∃ commonOutgoing ≥ (0 : ℝ),
    ∃ fullCommonIncoming ≥ (0 : ℝ), ∃ fullCommonOutgoing ≥ (0 : ℝ),
    ∃ fullSharpIncoming ≥ (0 : ℝ), ∃ fullSharpOutgoing ≥ (0 : ℝ),
    ∃ toleranceMax : ℝ → ℝ → ℝ,
    (∀ stableConstant ≥ (0 : ℝ), ∀ accuracy > (0 : ℝ), 0 < toleranceMax stableConstant accuracy) ∧
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ responseE ≥ (1 : ℝ), ∃ fullFollower ≥ (1 : ℝ),
    ∃ rootMin ≥ (8 : ℝ),
    let ownFollower := coarseConstant * responseE / 8
    let ownMagnitude := 1 + 8 * (4 * outgoingConstant + 1) + 32 * ownFollower * (4 * commonOutgoing + 1)
    let fullMagnitude := 1 + 8 * (4 * fullSharpOutgoing + 1) + 32 * fullFollower * (4 * fullCommonOutgoing + 1)
    ∀ stableConstant ≥ (0 : ℝ), ∀ accuracy > (0 : ℝ),
    ∀ extent magnitudeMax distanceMax coefficient : ℝ,
    1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < coefficient →
    ∃ ratioMin ≥ (2 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant chartConstant tolerance timingError : ℝ),
    1 ≤ boundaryConstant → 0 ≤ chartConstant → 0 ≤ tolerance → tolerance ≤ toleranceMax stableConstant accuracy → 0 ≤ timingError →
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
    (∀ time ∈ Icc 0 finish, |radialShape motion time receiver| ≤ 1 / 2) →
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
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    let ownForcing := fun time => ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid motion current receiver patch) ownRadius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) ownRadius (power + 1) time‖
    let first := motion
    let second := prepared.reference
    let omega := changed.omega (receiver.val + 1)
    let length := changed.length (receiver.val + 1)
    let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
    let epsilon := changed.radius (receiver.val + 1) ^ 2 / length ^ 2
    let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
    let relative := fun time => referenceStraightenedShape first graph coordinate receiver time - referenceStraightenedShape second graph coordinate receiver time
    let shape := fun time => |(relative time).1| + |(relative time).2|
    let moment := fun time => ‖relativeNormalizedFirstMoment changed first second receiver time‖
    let center := fun time => prepared.rawSourceCenteredState time receiver
    let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
    let dilation := fun time => |diagonalDifference first time receiver - diagonalDifference second time receiver| / length ^ 2
    let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time receiver
    let difference := fun time => ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first receiver time macroRadius power -
      quadrupoleExteriorCoefficient changed second receiver time macroRadius power‖
    let forcing := fun time => |(leading time).2| + tolerance * (moment time + center time + shape time) +
      stableConstant * omega * epsilon * (center time + raw time) + stableConstant * epsilon * ownForcing time +
      stableConstant * (length / macroRadius) * (changed.strain * center time + difference time) + stableConstant * referenceSize * ‖leading time‖
    let additive := fun time => tolerance * (moment time + center time + shape time) +
      stableConstant * omega * epsilon * (center time + raw time) + stableConstant * epsilon * ownForcing time +
      stableConstant * (length / macroRadius) * (changed.strain * center time + difference time) +
      stableConstant * referenceSize * ‖leading time‖ + stableConstant * omega * referenceSize * dilation time
    let drive := fun time => ‖leading time‖ + (forcing time - |(leading time).2| + stableConstant * omega * referenceSize * dilation time)
    let stateBudget := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time + raw time
    let origin := entry ⟨receiver.val + 1, nonterminal⟩
    (∀ time : ℝ, additive time = drive time - ‖leading time‖) ∧
    (∀ time ∈ Icc 0 finish, 0 ≤ additive time) ∧ ContinuousOn additive (Icc 0 finish) ∧
    ContinuousOn stateBudget (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * additive time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * stateBudget time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * additive time) ≤
      accuracy * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * stateBudget time) +
        (accuracy / 3) * (ownMagnitude + fullMagnitude) * changed.seed (receiver.val + 1) *
          Real.exp (-weight * origin) := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, closureCap, closurePositive,
    coarseConstant, coarseNonnegative, incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    fullCommonIncoming, fullCommonIncomingNonnegative, fullCommonOutgoing, fullCommonOutgoingNonnegative,
    fullSharpIncoming, fullSharpIncomingNonnegative, fullSharpOutgoing, fullSharpOutgoingNonnegative,
    toleranceMax, tolerancePositive, closures⟩ :=
    exists_uniform_actual_given_map_additive_weighted_closure_factor_uniform graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨stateCap, statePositive, states⟩ := exists_uniform_actual_source_state_continuity
  obtain ⟨geometryRadius, geometryPositive, _, _, _, geometries⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  let rawCap := min closureCap stateCap
  have rawPositive : 0 < rawCap := lt_min closurePositive statePositive
  have closureCapBound : rawCap ≤ closureCap := min_le_left _ _
  have stateCapBound : rawCap ≤ stateCap := min_le_right _ _
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive,
    coarseConstant, coarseNonnegative, incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    fullCommonIncoming, fullCommonIncomingNonnegative, fullCommonOutgoing, fullCommonOutgoingNonnegative,
    fullSharpIncoming, fullSharpIncomingNonnegative, fullSharpOutgoing, fullSharpOutgoingNonnegative,
    toleranceMax, tolerancePositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨closureRadius, closureRadiusPositive, closureQuarter, responseE, responseEOne, fullFollower, fullFollowerOne,
    parentRatio, parentTwo, rootMin, rootEight, closureFactory⟩ := closures factor factorPositive factorSmall
  let radius := min closureRadius geometryRadius
  have radiusQuarter : radius ≤ 1 / 4 := (min_le_left _ _).trans closureQuarter
  refine ⟨radius, lt_min closureRadiusPositive geometryPositive, radiusQuarter, responseE, responseEOne,
    fullFollower, fullFollowerOne, rootMin, rootEight, ?_⟩
  dsimp only
  let ownFollower := coarseConstant * responseE / 8
  have ownFollowerNonnegative : 0 ≤ ownFollower := div_nonneg
    (mul_nonneg coarseNonnegative (zero_le_one.trans responseEOne)) (by norm_num)
  obtain ⟨_, ownCalibrations⟩ := exists_uniform_calibrated_timed_known_source_budget_of_domains
    incomingNonnegative outgoingNonnegative commonIncomingNonnegative commonOutgoingNonnegative ownFollowerNonnegative
  obtain ⟨_, fullCalibrations⟩ := exists_uniform_calibrated_timed_known_source_budget_of_domains
    fullSharpIncomingNonnegative fullSharpOutgoingNonnegative fullCommonIncomingNonnegative fullCommonOutgoingNonnegative
    (zero_le_one.trans fullFollowerOne)
  intro stableConstant stableNonnegative accuracy accuracyPositive
  intro extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  obtain ⟨ownRatio, _, ownDomains⟩ :=
    ownCalibrations extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  obtain ⟨fullRatio, _, fullDomains⟩ :=
    fullCalibrations extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  let ratioMin := max parentRatio (max ownRatio fullRatio)
  refine ⟨ratioMin, parentTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant referenceNonnegative
    referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant chartConstant tolerance timingError boundaryOne
    chartNonnegative toleranceNonnegative toleranceSmall timingErrorNonnegative ratioSeparation
  have ratioBound : 2 ≤ scales.ratio := (parentTwo.trans (le_max_left _ _)).trans ratioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have growthOne : 1 ≤ 2 * Real.sqrt 2 := by
    have lower : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    linarith only [lower]
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  filter_upwards [closureFactory stableConstant stableNonnegative accuracy accuracyPositive scales scaleRoot rootLarge amplitudeIdentity ((le_max_left _ _).trans ratioLarge)
      alphaPositive extent extentOne referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime
      boundaryConstant chartConstant tolerance boundaryOne chartNonnegative toleranceNonnegative toleranceSmall,
    ownDomains scales amplitudePositive ((le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge))
      alphaPositive alphaSmall ratioPower (2 * Real.sqrt 2) timingError growthOne timingErrorNonnegative ratioSeparation
      sectionTime scaleRoot boundaryConstant (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    fullDomains scales amplitudePositive ((le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge))
      alphaPositive alphaSmall ratioPower (2 * Real.sqrt 2) timingError growthOne timingErrorNonnegative ratioSeparation
      sectionTime scaleRoot boundaryConstant (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    geometries scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) factorPositive (factorSmall.trans (by norm_num)) thresholdSmall referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    eventually_ge_atTop (1 : ℝ)]
    with frequency closureEstimate ownEstimate fullEstimate geometryEstimate coherence frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal entry initialDistance direction entries extents
    magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
    finish finishInside radialSmall small suppliedLift suppliedContinuous suppliedInitial suppliedPolar rateBounds
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (receiver.val + 1)
  let weight := 2 * Real.sqrt 2 * omega
  let location := changed.location (receiver.val + 1)
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let origin := entry ⟨receiver.val + 1, nonterminal⟩
  let ownMagnitude := 1 + 8 * (4 * outgoingConstant + 1) + 32 * ownFollower * (4 * commonOutgoing + 1)
  let fullMagnitude := 1 + 8 * (4 * fullSharpOutgoing + 1) + 32 * fullFollower * (4 * fullCommonOutgoing + 1)
  let sharpBudget := fun incoming outgoing =>
    prepared.mixedSelectedFinerSourcePrefixBudget receiver incoming outgoing extent coefficient entry initialDistance magnitude weight finish
  let commonBudget := fun incoming outgoing =>
    prepared.mixedFollowerSourcePrefixBudget receiver incoming outgoing extent coefficient entry initialDistance magnitude weight finish
  let ownBudget := sharpBudget incomingConstant outgoingConstant +
    (4 * coarseConstant * responseE * rho / (weight * location ^ 4)) * commonBudget commonIncoming commonOutgoing
  let ownKnown := 8 * sharpBudget incomingConstant outgoingConstant +
    (32 * ownFollower * rho / (omega * location ^ 4)) * commonBudget commonIncoming commonOutgoing
  let fullKnown := 8 * sharpBudget fullSharpIncoming fullSharpOutgoing +
    (32 * fullFollower * rho / (omega * location ^ 4)) * commonBudget fullCommonIncoming fullCommonOutgoing
  have rawInvariant : (prepared.enlargeCap closureCapBound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have sizeInvariant : (prepared.enlargeCap closureCapBound).finiteCoordinateSize = prepared.finiteCoordinateSize := rfl
  have sharpInvariant : (prepared.enlargeCap closureCapBound).mixedSelectedFinerSourcePrefixBudget =
      prepared.mixedSelectedFinerSourcePrefixBudget := rfl
  have commonInvariant : (prepared.enlargeCap closureCapBound).mixedFollowerSourcePrefixBudget =
      prepared.mixedFollowerSourcePrefixBudget := rfl
  have actual := closureEstimate count phase dipoleAngle (prepared.enlargeCap closureCapBound) path receiver nonterminal path.stop
    path.stopPositive.le le_rfl entry initialDistance direction entries extents coefficient coefficientPositive magnitude
    (by simpa only [rawInvariant] using profiles) finish finishInside radialSmall
    (fun current below time inside => (small current below time inside).trans (min_le_left _ _))
    suppliedLift suppliedContinuous suppliedInitial suppliedPolar rateBounds
  dsimp only at actual
  simp only [rawInvariant, sizeInvariant, sharpInvariant, commonInvariant] at actual
  have sourceEntries (source : Fin count) (below : receiver.val < source.val) : entry source ∈ Icc 0 path.stop :=
    ⟨(entries source below).1, (entries source below).2.1⟩
  have magnitudeBounds (source : Fin count) (below : receiver.val < source.val) :
      0 ≤ magnitude source ∧ magnitude source ≤ magnitudeMax := ⟨(profiles source below).1, magnitudeUpper source below⟩
  have distanceBounds (source : Fin count) (below : receiver.val < source.val) :
      0 ≤ initialDistance source ∧ initialDistance source ≤ distanceMax :=
    ⟨(by norm_num : (0 : ℝ) ≤ 512).trans (entries source below).2.2.1, distanceUpper source below⟩
  have ownData := ownEstimate count (thresholdSmall.trans (by norm_num)) (factorSmall.trans (by norm_num))
    prepared path receiver nonterminal entry initialDistance magnitude actualTime timeIdentity sourceEntries nearestTiming sourceTiming
    timeOrder magnitudeBounds distanceBounds domains finish
  have fullData := fullEstimate count (thresholdSmall.trans (by norm_num)) (factorSmall.trans (by norm_num))
    prepared path receiver nonterminal entry initialDistance magnitude actualTime timeIdentity sourceEntries nearestTiming sourceTiming
    timeOrder magnitudeBounds distanceBounds domains finish
  have ownBound : ownKnown ≤ ownMagnitude * changed.seed (receiver.val + 1) * Real.exp (-weight * origin) := ownData.2
  have fullBound : fullKnown ≤ fullMagnitude * changed.seed (receiver.val + 1) * Real.exp (-weight * origin) := fullData.2
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := lt_of_lt_of_le (by norm_num) ratioBound
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have locationPositive : 0 < location := changed.location_pos _
  have omegaWeight : omega ≤ weight := by
    have lower : (1 : ℝ) ≤ 2 * Real.sqrt 2 := growthOne
    exact le_mul_of_one_le_left omegaPositive.le lower
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho]
    positivity
  have sharpNonnegative : 0 ≤ sharpBudget incomingConstant outgoingConstant := by
    dsimp only [sharpBudget, CascadeSourcePreparedPair.mixedSelectedFinerSourcePrefixBudget]
    apply add_nonneg
    · apply mul_nonneg (mul_nonneg incomingNonnegative (sq_nonneg extent))
      apply Finset.sum_nonneg
      intro source member
      have below := (Finset.mem_filter.mp member).2
      have sourceMagnitude := (magnitudeBounds source below).1
      have circulation := changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)
      have sourceOmega := changed.omega_pos frequencyPositive ratioPositive (source.val + 1)
      have sourceLocation := changed.location_pos (source.val + 1)
      positivity
    · apply mul_nonneg (div_nonneg outgoingNonnegative (pow_nonneg locationPositive.le 4))
      apply Finset.sum_nonneg
      intro source member
      have below := (Finset.mem_filter.mp (Finset.mem_filter.mp member).1).2
      have sourceDistance := (distanceBounds source below).1
      have circulation := changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)
      positivity
  have commonNonnegative : 0 ≤ commonBudget commonIncoming commonOutgoing := by
    dsimp only [commonBudget, CascadeSourcePreparedPair.mixedFollowerSourcePrefixBudget]
    apply add_nonneg
    · apply mul_nonneg (mul_nonneg commonIncomingNonnegative (sq_nonneg extent))
      apply Finset.sum_nonneg
      intro source member
      have below := (Finset.mem_filter.mp member).2
      have sourceMagnitude := (magnitudeBounds source below).1
      have circulation := changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)
      have sourceOmega := changed.omega_pos frequencyPositive ratioPositive (source.val + 1)
      have sourceLocation := changed.location_pos (source.val + 1)
      positivity
    · apply mul_nonneg commonOutgoingNonnegative
      apply Finset.sum_nonneg
      intro source member
      have below := (Finset.mem_filter.mp (Finset.mem_filter.mp member).1).2
      have sourceDistance := (distanceBounds source below).1
      have circulation := changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)
      positivity
  have returnedCoefficient : 4 * coarseConstant * responseE * rho / (weight * location ^ 4) ≤
      32 * ownFollower * rho / (omega * location ^ 4) := by
    have identity : 32 * ownFollower * rho / (omega * location ^ 4) =
        4 * coarseConstant * responseE * rho / (omega * location ^ 4) := by dsimp only [ownFollower]; ring
    rw [identity]
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos omegaPositive (pow_pos locationPositive 4))
      (mul_le_mul_of_nonneg_right omegaWeight (pow_nonneg locationPositive.le 4))
  have ownComparison : ownBudget ≤ ownKnown := add_le_add
    (le_mul_of_one_le_left sharpNonnegative (by norm_num : (1 : ℝ) ≤ 8))
    (mul_le_mul_of_nonneg_right returnedCoefficient commonNonnegative)
  have budgetBound : ownBudget + fullKnown ≤ (ownMagnitude + fullMagnitude) * changed.seed (receiver.val + 1) *
      Real.exp (-weight * origin) := by
    exact (add_le_add (ownComparison.trans ownBound) fullBound).trans_eq (by ring)
  obtain ⟨geometryLift, geometryProperties, geometryPolar, geometryContinuous, _, _, _⟩ :=
    geometryEstimate prepared path receiver nonterminal finish finishInside.1 finishInside.2
      (fun time inside => (small receiver le_rfl time inside).trans (min_le_right _ _))
  have equality := (coherence prepared path receiver finish finishInside.1 finishInside.2
    (fun time inside => (small receiver le_rfl time inside).trans radiusQuarter)
    geometryLift suppliedLift (fun side => (geometryProperties side).1.continuousOn) suppliedContinuous
    (fun side => (geometryProperties side).2.trans (suppliedInitial side).symm) geometryPolar suppliedPolar).2.2 graph coordinate
  have sizeContinuous := geometryContinuous.congr (fun time inside => (equality inside).symm)
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishInside.2
  have rawContinuous := continuousOn_finset_sum Finset.univ
    (fun patch _ => ((states prepared rawPositive stateCapBound path receiver).1 patch).mono subset)
  refine ⟨actual.1, actual.2.1, actual.2.2.1, sizeContinuous.add rawContinuous, actual.2.2.2.1, actual.2.2.2.2.1, ?_⟩
  have scaled := mul_le_mul_of_nonneg_left budgetBound (div_nonneg accuracyPositive.le (by norm_num : (0 : ℝ) ≤ 3))
  have adjusted : (accuracy / 3) *
      (sharpBudget incomingConstant outgoingConstant +
        (4 * coarseConstant * responseE * rho / (weight * location ^ 4)) * commonBudget commonIncoming commonOutgoing +
        8 * sharpBudget fullSharpIncoming fullSharpOutgoing +
        (32 * fullFollower * rho / (omega * location ^ 4)) * commonBudget fullCommonIncoming fullCommonOutgoing) ≤
      (accuracy / 3) * ((ownMagnitude + fullMagnitude) * changed.seed (receiver.val + 1) * Real.exp (-weight * origin)) := by
    simpa only [ownBudget, fullKnown, add_assoc] using scaled
  have enlarged := actual.2.2.2.2.2.trans (add_le_add_left adjusted _)
  convert enlarged using 1
  dsimp only [ownBudget, fullKnown, sharpBudget, commonBudget]
  ring

theorem exists_uniform_actual_domain_additive_weighted_closure
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ coarseConstant ≥ (0 : ℝ), ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∃ commonIncoming ≥ (0 : ℝ), ∃ commonOutgoing ≥ (0 : ℝ),
    ∃ fullCommonIncoming ≥ (0 : ℝ), ∃ fullCommonOutgoing ≥ (0 : ℝ),
    ∃ fullSharpIncoming ≥ (0 : ℝ), ∃ fullSharpOutgoing ≥ (0 : ℝ),
    ∀ stableConstant ≥ (0 : ℝ), ∀ accuracy > (0 : ℝ), ∃ toleranceMax > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ responseE ≥ (1 : ℝ), ∃ fullFollower ≥ (1 : ℝ),
    ∃ rootMin ≥ (8 : ℝ),
    let ownFollower := coarseConstant * responseE / 8
    let ownMagnitude := 1 + 8 * (4 * outgoingConstant + 1) + 32 * ownFollower * (4 * commonOutgoing + 1)
    let fullMagnitude := 1 + 8 * (4 * fullSharpOutgoing + 1) + 32 * fullFollower * (4 * fullCommonOutgoing + 1)
    ∀ extent magnitudeMax distanceMax coefficient : ℝ,
    1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < coefficient →
    ∃ ratioMin ≥ (2 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant chartConstant tolerance timingError : ℝ),
    1 ≤ boundaryConstant → 0 ≤ chartConstant → 0 ≤ tolerance → tolerance ≤ toleranceMax → 0 ≤ timingError →
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
    (∀ time ∈ Icc 0 finish, |radialShape motion time receiver| ≤ 1 / 2) →
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
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    let ownForcing := fun time => ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid motion current receiver patch) ownRadius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) ownRadius (power + 1) time‖
    let first := motion
    let second := prepared.reference
    let omega := changed.omega (receiver.val + 1)
    let length := changed.length (receiver.val + 1)
    let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
    let epsilon := changed.radius (receiver.val + 1) ^ 2 / length ^ 2
    let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
    let relative := fun time => referenceStraightenedShape first graph coordinate receiver time - referenceStraightenedShape second graph coordinate receiver time
    let shape := fun time => |(relative time).1| + |(relative time).2|
    let moment := fun time => ‖relativeNormalizedFirstMoment changed first second receiver time‖
    let center := fun time => prepared.rawSourceCenteredState time receiver
    let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
    let dilation := fun time => |diagonalDifference first time receiver - diagonalDifference second time receiver| / length ^ 2
    let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time receiver
    let difference := fun time => ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first receiver time macroRadius power -
      quadrupoleExteriorCoefficient changed second receiver time macroRadius power‖
    let forcing := fun time => |(leading time).2| + tolerance * (moment time + center time + shape time) +
      stableConstant * omega * epsilon * (center time + raw time) + stableConstant * epsilon * ownForcing time +
      stableConstant * (length / macroRadius) * (changed.strain * center time + difference time) + stableConstant * referenceSize * ‖leading time‖
    let additive := fun time => tolerance * (moment time + center time + shape time) +
      stableConstant * omega * epsilon * (center time + raw time) + stableConstant * epsilon * ownForcing time +
      stableConstant * (length / macroRadius) * (changed.strain * center time + difference time) +
      stableConstant * referenceSize * ‖leading time‖ + stableConstant * omega * referenceSize * dilation time
    let drive := fun time => ‖leading time‖ + (forcing time - |(leading time).2| + stableConstant * omega * referenceSize * dilation time)
    let stateBudget := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time + raw time
    let origin := entry ⟨receiver.val + 1, nonterminal⟩
    (∀ time : ℝ, additive time = drive time - ‖leading time‖) ∧
    (∀ time ∈ Icc 0 finish, 0 ≤ additive time) ∧ ContinuousOn additive (Icc 0 finish) ∧
    ContinuousOn stateBudget (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * additive time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * stateBudget time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * additive time) ≤
      accuracy * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * stateBudget time) +
        (accuracy / 3) * (ownMagnitude + fullMagnitude) * changed.seed (receiver.val + 1) *
          Real.exp (-weight * origin) := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    coarseConstant, coarseNonnegative, incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    fullCommonIncoming, fullCommonIncomingNonnegative, fullCommonOutgoing, fullCommonOutgoingNonnegative,
    fullSharpIncoming, fullSharpIncomingNonnegative, fullSharpOutgoing, fullSharpOutgoingNonnegative,
    toleranceMax, tolerancePositive, factors⟩ :=
    exists_uniform_actual_domain_additive_weighted_closure_factor_uniform graphAnalytic coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    coarseConstant, coarseNonnegative, incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    fullCommonIncoming, fullCommonIncomingNonnegative, fullCommonOutgoing, fullCommonOutgoingNonnegative,
    fullSharpIncoming, fullSharpIncomingNonnegative, fullSharpOutgoing, fullSharpOutgoingNonnegative, ?_⟩
  intro stableConstant stableNonnegative accuracy accuracyPositive
  refine ⟨toleranceMax stableConstant accuracy, tolerancePositive stableConstant stableNonnegative accuracy accuracyPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, responseE, responseEOne, fullFollower, fullFollowerOne,
    rootMin, rootEight, factory⟩ := factors factor factorPositive factorSmall
  exact ⟨radius, radiusPositive, radiusQuarter, responseE, responseEOne, fullFollower, fullFollowerOne,
    rootMin, rootEight, factory stableConstant stableNonnegative accuracy accuracyPositive⟩

end EulerNonuniqueness.Paper

