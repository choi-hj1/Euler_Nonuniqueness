import EulerNonuniqueness.Section5.CascadeShapeProfileStrictCoefficientCost
import EulerNonuniqueness.Section5.CascadeCalibratedKnownSourceBudgetFromDomains

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_domain_shape_profile_strict_cost :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ),
      ∃ commonIncoming ≥ (0 : ℝ), ∃ commonOutgoing ≥ (0 : ℝ),
      ∃ sharpIncoming ≥ (0 : ℝ), ∃ sharpOutgoing ≥ (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ stableConstant ≥ (1 : ℝ), ∃ dilationConstant ≥ (0 : ℝ), ∃ constant ≥ (1 : ℝ),
      ∃ profileConstant ≥ (1 : ℝ), ∃ followerConstant ≥ (1 : ℝ),
      ∃ rootMin ≥ (8 : ℝ),
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      let sourceMagnitude := 1 + 8 * (4 * sharpOutgoing + 1) + 32 * followerConstant * (4 * commonOutgoing + 1)
      ∀ shapeMagnitude actionTolerance : ℝ, 0 ≤ shapeMagnitude → 0 < actionTolerance →
      ∃ endpointSize > (0 : ℝ),
      ∀ extent magnitudeMax distanceMax sourceRate : ℝ,
      1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < sourceRate →
      ∃ ratioMin ≥ max 2 (4 * followerConstant),
      ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
      ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
      ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
      ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant tolerance timingError : ℝ),
      1 ≤ boundaryConstant → 0 < tolerance → tolerance ≤ 1 → 0 ≤ timingError →
      (2 * Real.sqrt 2 + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ (index : Fin count) (nonterminal : index.val + 1 < count),
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
      ∀ finish ∈ Icc 0 path.stop,
      (∀ time ∈ Icc 0 finish, |radialShape motion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 finish, |unstableShape motion time index| + |stableShape motion time index| ≤ radius) →
      (∀ receiver : Fin count, receiver.val < index.val → ∀ time ∈ Icc 0 finish,
        |unstableShape motion time receiver| + |stableShape motion time receiver| ≤ radius) →
      (∀ source : Fin count, index.val < source.val →
        2 * (2 * Real.sqrt 2 * changed.omega (index.val + 1)) ≤ sourceRate * changed.omega (source.val + 1)) →
      ∀ suppliedLift : Fin 2 → ℝ → ℝ,
      (∀ side, ContinuousOn (suppliedLift side) (Icc 0 finish)) →
      (∀ side, suppliedLift side 0 = phase (index.val + 1)) →
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (suppliedLift side time : ℂ))) →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let relative := fun time => referenceStraightenedShape first graph coordinate index time -
        referenceStraightenedShape second graph coordinate index time
      let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time index
      let remainder := relativeStraightenedSaddleStrainRemainder changed
        (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate index
      let omega := changed.omega (index.val + 1)
      let growth := 2 * Real.sqrt 2 * omega
      let length := changed.length (index.val + 1)
      let centerRadius := factor / 39321600 * changed.location (index.val + 1)
      let patchRadius := factor / 39321600 * length
      let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
      let center := fun time => prepared.rawSourceCenteredState time index
      let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
      let moment := fun time => ‖relativeNormalizedFirstMoment changed first second index time‖
      let shape := fun time => |(relative time).1| + |(relative time).2|
      let dilation := fun time => |diagonalDifference first time index - diagonalDifference second time index| / length ^ 2
      let indexedReferenceSize := chartConstant * referenceConstant *
        ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
      let coefficient := fun time => indexedReferenceSize + dilation time + |(relative time).2|
      let graded := fun time => coefficient time * shape time + indexedReferenceSize * dilation time
      let difference := fun time => ∑' power : ℕ,
        ‖quadrupoleExteriorCoefficient changed first index time centerRadius power -
          quadrupoleExteriorCoefficient changed second index time centerRadius power‖
      let firstFamily := prepared.trajectory.movingFamily
      let secondFamily := prepared.referenceWitness.trajectory.movingFamily
      let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖firstFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid firstFamily.patchMotion current index patch) patchRadius (power + 1) time -
          secondFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid secondFamily.patchMotion current index patch) patchRadius (power + 1) time‖
      let dilationMajorant := fun time => tolerance * moment time +
        (tolerance + dilationConstant * changed.strain + dilationConstant * omega * epsilon) * center time +
        dilationConstant * omega * epsilon * raw time + dilationConstant * difference time +
        dilationConstant * epsilon * ∑ patch : Fin 4, foreign patch time
      let forcing := fun time => |(leading time).2| + tolerance * (moment time + center time + shape time) +
        stableConstant * omega * epsilon * (center time + raw time) +
        stableConstant * epsilon * ∑ patch : Fin 4, foreign patch time +
        stableConstant * (length / centerRadius) * (changed.strain * center time + difference time) +
        stableConstant * indexedReferenceSize * ‖leading time‖
      let upper := fun time => stableConstant * omega * graded time + tolerance * (moment time + center time + shape time) +
        stableConstant * omega * epsilon * (center time + raw time) +
        stableConstant * epsilon * ∑ patch : Fin 4, foreign patch time +
        stableConstant * (length / centerRadius) * (changed.strain * center time + difference time) +
        stableConstant * indexedReferenceSize * ‖leading time‖
      let drive := fun time => ‖leading time‖ + (forcing time - |(leading time).2|) +
        stableConstant * omega * indexedReferenceSize * dilation time
      let actionCost := 2 * omega * indexedReferenceSize * finish +
        2 * omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationMajorant time) +
        ∫ time in (0 : ℝ)..finish, forcing time
      let additive := fun time => drive time - ‖leading time‖
      let error := fun time => 2 * stableConstant * actionCost * Real.exp (2 * stableConstant * actionCost) *
        (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * drive current) +
        ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * additive current
      let origin := entry ⟨index.val + 1, nonterminal⟩
      let state := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift index time + raw time
      let allForeign := prepared.selectedForeignForcing (Finset.univ.erase index) index
      (∀ time ∈ Icc 0 finish, shape time ≤ shapeMagnitude * changed.seed (index.val + 1) *
        Real.exp (growth * (time - origin))) →
      changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) ≤ endpointSize →
      (((ContinuousOn coefficient (Icc 0 finish) ∧ ContinuousOn dilationMajorant (Icc 0 finish) ∧
      ContinuousOn forcing (Icc 0 finish) ∧
      IntervalIntegrable coefficient volume 0 finish ∧
      IntervalIntegrable (fun time => (finish - time) * dilationMajorant time) volume 0 finish ∧
      IntervalIntegrable forcing volume 0 finish ∧
      (omega * (∫ time in (0 : ℝ)..finish, coefficient time) ≤
        2 * omega * indexedReferenceSize * finish +
          2 * omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationMajorant time) +
          ∫ time in (0 : ℝ)..finish, forcing time) ∧
      0 < growth ∧ ContinuousOn relative (Icc 0 finish) ∧ ContinuousOn leading (Icc 0 finish) ∧
      ContinuousOn remainder (Icc 0 finish) ∧
      IntervalIntegrable (fun time => ‖remainder time‖) volume 0 finish ∧
      IntervalIntegrable upper volume 0 finish ∧
      (∀ time ∈ Ioo 0 finish, ‖remainder time‖ ≤ upper time) ∧
      (∀ time ∈ Icc 0 finish,
        (∫ current in (0 : ℝ)..time, ‖remainder current‖) ≤ ∫ current in (0 : ℝ)..time, upper current ∧
        Real.exp (-growth * time) * (relative time).1 =
          (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (leading current).1) +
            ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (remainder current).1 ∧
        (relative time).2 = ∫ current in (0 : ℝ)..time,
          Real.exp (-growth * (time - current)) * (leading current + remainder current).2 ∧
        |(relative time).2| ≤ ∫ current in (0 : ℝ)..time,
          Real.exp (-growth * (time - current)) * (|(leading current).2| + upper current)) ∧
      growth * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(relative time).2|) ≤
        (1 / 2 : ℝ) * ((∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(leading time).2|) +
          ∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * upper time)) ∧
      ContinuousOn drive (Icc 0 finish) ∧ IntervalIntegrable drive volume 0 finish ∧
      ∀ time ∈ Icc 0 finish,
        IntervalIntegrable (fun current => Real.exp (-growth * current) * drive current) volume 0 time ∧
        Real.exp (-growth * time) * shape time ≤
          2 * Real.exp (2 * stableConstant * omega * (∫ current in (0 : ℝ)..time, coefficient current)) *
            ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * drive current ∧
        Real.exp (-growth * time) * shape time ≤
          2 * Real.exp (2 * stableConstant * actionCost) *
            ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * drive current) ∧
      ContinuousOn additive (Icc 0 finish) ∧ IntervalIntegrable additive volume 0 finish ∧
      ∀ time ∈ Icc 0 finish,
        IntervalIntegrable (fun current => Real.exp (-growth * current) * ‖remainder current‖) volume 0 time ∧
        IntervalIntegrable (fun current => Real.exp (-growth * current) * additive current) volume 0 time ∧
        IntervalIntegrable (fun current => Real.exp (-growth * current) * (leading current).1) volume 0 time ∧
        (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * ‖remainder current‖) ≤ error time ∧
        (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (leading current).1) - error time ≤
          Real.exp (-growth * time) * (relative time).1) ∧
      ContinuousOn state (Icc 0 finish) ∧ ContinuousOn allForeign (Icc 0 finish) ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * allForeign time) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * shape time) volume 0 finish ∧
      (∀ time ∈ Icc 0 finish, prepared.finiteCoordinateForeignForcing index time +
        prepared.physicalForeignSourceForcing index time ≤ allForeign time) ∧
      (∀ time ∈ Icc 0 finish, state time ≤ profileConstant * (2 * shapeMagnitude + sourceMagnitude) *
        changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) ∧
      (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * allForeign time) ≤
        (shapeMagnitude + sourceMagnitude) * changed.seed (index.val + 1) * Real.exp (-growth * origin) ∧
      actionCost ≤ 2 * omega * indexedReferenceSize * finish +
        3 * constant * (profileConstant * (2 * shapeMagnitude + sourceMagnitude) + shapeMagnitude + sourceMagnitude) *
          changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) ∧
      actionCost < actionTolerance ∧ omega * (∫ time in (0 : ℝ)..finish, coefficient time) < actionTolerance := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth, compatible, rawCap, rawPositive,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    sharpIncoming, sharpIncomingNonnegative, sharpOutgoing, sharpOutgoingNonnegative, strictFactory⟩ :=
    exists_uniform_actual_shape_profile_strict_coefficient_cost
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth, compatible, rawCap, rawPositive,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    sharpIncoming, sharpIncomingNonnegative, sharpOutgoing, sharpOutgoingNonnegative, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, constant, constantOne,
    profileConstant, profileOne, followerConstant, followerOne, parentRatio, parentMinimum, rootMin, rootEight,
    radius, radiusPositive, radiusQuarter, stricts⟩ := strictFactory factorPositive factorSmall
  refine ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, constant, constantOne,
    profileConstant, profileOne, followerConstant, followerOne, rootMin, rootEight, radius, radiusPositive, radiusQuarter, ?_⟩
  dsimp only
  let sourceMagnitude := 1 + 8 * (4 * sharpOutgoing + 1) + 32 * followerConstant * (4 * commonOutgoing + 1)
  obtain ⟨sourceOne, calibrations⟩ := exists_uniform_calibrated_timed_known_source_budget_of_domains
    sharpIncomingNonnegative sharpOutgoingNonnegative commonIncomingNonnegative commonOutgoingNonnegative
    (zero_le_one.trans followerOne)
  intro shapeMagnitude actionTolerance shapeNonnegative actionPositive
  obtain ⟨endpointSize, endpointPositive, endpoints⟩ :=
    stricts shapeMagnitude sourceMagnitude actionTolerance shapeNonnegative (zero_le_one.trans sourceOne) actionPositive
  refine ⟨endpointSize, endpointPositive, ?_⟩
  intro extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  obtain ⟨calibratedRatio, calibratedTwo, domainsFactory⟩ :=
    calibrations extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  let ratioMin := max parentRatio calibratedRatio
  refine ⟨ratioMin, parentMinimum.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant referenceNonnegative
    referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant tolerance timingError boundaryOne
    tolerancePositive toleranceOne timingErrorNonnegative ratioSeparation
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have growthOne : 1 ≤ 2 * Real.sqrt 2 := by
    have lower : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    linarith only [lower]
  filter_upwards [endpoints scales scaleRoot rootLarge amplitudeIdentity ((le_max_left _ _).trans ratioLarge) alphaPositive
      extent extentOne referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant
      tolerance boundaryOne tolerancePositive toleranceOne,
    domainsFactory scales amplitudePositive ((le_max_right _ _).trans ratioLarge) alphaPositive alphaSmall ratioPower
      (2 * Real.sqrt 2) timingError growthOne timingErrorNonnegative ratioSeparation sectionTime scaleRoot boundaryConstant
      (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne)] with frequency strictEstimate domainEstimate
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal entry initialDistance direction
  intro entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming
    sourceTiming timeOrder finish finishInside radialSmall targetSmall followerSmall sourceRates
    suppliedLift suppliedContinuous suppliedInitial suppliedPolar shapeProfile endpointBound
  have actual := strictEstimate count phase dipoleAngle prepared path index nonterminal path.stop path.stopPositive.le le_rfl
    entry initialDistance direction entries extents sourceRate sourceRatePositive magnitude sourceProfiles finish finishInside
    radialSmall targetSmall followerSmall sourceRates
  have known := domainEstimate count (thresholdBound.trans (thresholdEighth.trans (by norm_num)))
    (factorSmall.trans (by norm_num)) prepared path index nonterminal entry initialDistance magnitude actualTime timeIdentity
    (fun source below => ⟨(entries source below).1, (entries source below).2.1⟩) nearestTiming sourceTiming timeOrder
    (fun source below => ⟨(sourceProfiles source below).1, magnitudeUpper source below⟩)
    (fun source below => ⟨(by norm_num : (0 : ℝ) ≤ 512).trans (entries source below).2.2.1, distanceUpper source below⟩)
    domains finish
  obtain ⟨stateContinuous, allContinuous, allIntegrable, _, shapeIntegrable, literalBound, response⟩ :=
    actual.2 suppliedLift suppliedContinuous suppliedInitial suppliedPolar
  have closed := response (entry ⟨index.val + 1, nonterminal⟩) shapeProfile known.2 endpointBound
  exact ⟨actual.1, stateContinuous, allContinuous, allIntegrable, shapeIntegrable, literalBound, closed⟩

end EulerNonuniqueness.Paper

