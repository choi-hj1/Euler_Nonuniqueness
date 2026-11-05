import EulerNonuniqueness.Section5.CascadeDomainShapeProfileStrictCost
import EulerNonuniqueness.Section5.CascadeDomainAdditiveWeightedClosure
import EulerNonuniqueness.Section5.CascadeDomainAllForeignWeightedClosure
import EulerNonuniqueness.General.WeightedExponentialProfileBootstrap

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_domain_shape_profile_improvement :
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
      ∃ rootMin ≥ (8 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ endpointSize > (0 : ℝ),
      ∀ extent magnitudeMax distanceMax sourceRate : ℝ,
      1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < sourceRate →
      ∃ ratioMin ≥ (2 : ℝ),
      ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
      ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
      ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
      ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant timingError : ℝ),
      1 ≤ boundaryConstant → 0 ≤ timingError →
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
      let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
      let shape := fun time =>
        |(referenceStraightenedShape motion graph coordinate index time).1 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
        |(referenceStraightenedShape motion graph coordinate index time).2 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).2|
      let origin := entry ⟨index.val + 1, nonterminal⟩
      (∀ time ∈ Icc 0 finish, shape time ≤ profileMagnitude * changed.seed (index.val + 1) *
        Real.exp (growth * (time - origin))) →
      changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) ≤ endpointSize →
      ContinuousOn shape (Icc 0 finish) ∧ shape 0 = 0 ∧
      shape finish ≤ (profileMagnitude / 2) * changed.seed (index.val + 1) *
        Real.exp (growth * (finish - origin)) := by
  dsimp only
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, costThreshold, costThresholdPositive, costEighth, compatible, costCap, costCapPositive,
    costCommonIncoming, costCommonIncomingNonnegative, costCommonOutgoing, costCommonOutgoingNonnegative,
    costSharpIncoming, costSharpIncomingNonnegative, costSharpOutgoing, costSharpOutgoingNonnegative, costFactors⟩ :=
    exists_uniform_actual_domain_shape_profile_strict_cost
  obtain ⟨addThreshold, addThresholdPositive, _, addCap, addCapPositive, coarseConstant, coarseNonnegative,
    addIncoming, addIncomingNonnegative, addOutgoing, addOutgoingNonnegative,
    addCommonIncoming, addCommonIncomingNonnegative, addCommonOutgoing, addCommonOutgoingNonnegative,
    addFullCommonIncoming, addFullCommonIncomingNonnegative, addFullCommonOutgoing, addFullCommonOutgoingNonnegative,
    addFullSharpIncoming, addFullSharpIncomingNonnegative, addFullSharpOutgoing, addFullSharpOutgoingNonnegative, additiveFactors⟩ :=
    exists_uniform_actual_domain_additive_weighted_closure graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨allThreshold, allThresholdPositive, _, allCap, allCapPositive,
    allCommonIncoming, allCommonIncomingNonnegative, allCommonOutgoing, allCommonOutgoingNonnegative,
    allSharpIncoming, allSharpIncomingNonnegative, allSharpOutgoing, allSharpOutgoingNonnegative, allFactors⟩ :=
    exists_uniform_actual_given_map_domain_all_foreign_weighted_closure graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  let thresholdMax := min costThreshold (min addThreshold allThreshold)
  let rawCap := min costCap (min addCap allCap)
  have costCapBound : rawCap ≤ costCap := min_le_left _ _
  have addCapBound : rawCap ≤ addCap := (min_le_right _ _).trans (min_le_left _ _)
  have allCapBound : rawCap ≤ allCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, thresholdMax, lt_min costThresholdPositive (lt_min addThresholdPositive allThresholdPositive),
    (min_le_left _ _).trans costEighth, compatible, rawCap, lt_min costCapPositive (lt_min addCapPositive allCapPositive), ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, constant, constantOne,
    profileConstant, profileOne, followerConstant, followerOne, costRoot, costEight,
    costRadius, costRadiusPositive, costQuarter, costs⟩ := costFactors factorPositive factorSmall
  let accuracy := 1 / (64 * (1 + profileConstant))
  have accuracyPositive : 0 < accuracy := by dsimp only [accuracy]; positivity
  obtain ⟨toleranceMax, tolerancePositive, additiveFactor⟩ :=
    additiveFactors stableConstant (zero_le_one.trans stableOne) accuracy accuracyPositive
  obtain ⟨addRadius, addRadiusPositive, _, responseE, responseEOne, fullFollower, fullFollowerOne,
    addRoot, addEight, additives⟩ := additiveFactor factor factorPositive factorSmall
  obtain ⟨allRadius, allRadiusPositive, _, allFollower, allFollowerOne, allRoot, allEight, alls⟩ :=
    allFactors factor factorPositive factorSmall
  let costMagnitude := 1 + 8 * (4 * costSharpOutgoing + 1) + 32 * followerConstant * (4 * costCommonOutgoing + 1)
  let leadingMagnitude := 1 + 8 * (4 * allSharpOutgoing + 1) + 32 * allFollower * (4 * allCommonOutgoing + 1)
  let additiveMagnitude :=
    (1 + 8 * (4 * addOutgoing + 1) + 32 * (coarseConstant * responseE / 8) * (4 * addCommonOutgoing + 1)) +
    (1 + 8 * (4 * addFullSharpOutgoing + 1) + 32 * fullFollower * (4 * addFullCommonOutgoing + 1))
  have costOne : 1 ≤ costMagnitude := by
    dsimp only [costMagnitude]
    have first : 0 ≤ 8 * (4 * costSharpOutgoing + 1) := by positivity
    have second : 0 ≤ 32 * followerConstant * (4 * costCommonOutgoing + 1) := by positivity
    linarith only [first, second]
  have leadingOne : 1 ≤ leadingMagnitude := by
    dsimp only [leadingMagnitude]
    have first : 0 ≤ 8 * (4 * allSharpOutgoing + 1) := by positivity
    have second : 0 ≤ 32 * allFollower * (4 * allCommonOutgoing + 1) := by positivity
    linarith only [first, second]
  have additiveNonnegative : 0 ≤ additiveMagnitude := by dsimp only [additiveMagnitude]; positivity
  let base := leadingMagnitude + accuracy * profileConstant * costMagnitude + (accuracy / 3) * additiveMagnitude
  have baseNonnegative : 0 ≤ base := by dsimp only [base]; positivity
  let profileMagnitude := 1 + 16 * base
  have magnitudeOne : 1 ≤ profileMagnitude := by dsimp only [profileMagnitude]; linarith only [baseNonnegative]
  let actionTolerance := Real.log 2 / (2 * stableConstant)
  have actionPositive : 0 < actionTolerance := div_pos (Real.log_pos (by norm_num)) (by positivity)
  obtain ⟨endpointSize, endpointPositive, endpointFactories⟩ :=
    costs profileMagnitude actionTolerance (zero_le_one.trans magnitudeOne) actionPositive
  let tolerance := min 1 toleranceMax
  have toleranceChosenPositive : 0 < tolerance := lt_min (by norm_num) tolerancePositive
  let rootMin := max costRoot (max addRoot allRoot)
  let radius := min costRadius (min addRadius allRadius)
  refine ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne, leadingMagnitude, leadingOne,
    additiveMagnitude, additiveNonnegative, magnitudeOne, rootMin, costEight.trans (le_max_left _ _),
    radius, lt_min costRadiusPositive (lt_min addRadiusPositive allRadiusPositive), (min_le_left _ _).trans costQuarter,
    endpointSize, endpointPositive, ?_⟩
  intro extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  obtain ⟨costRatio, costMinimum, costFactory⟩ := endpointFactories extent magnitudeMax distanceMax sourceRate
    extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  obtain ⟨addRatio, addTwo, addFactory⟩ := additives extent magnitudeMax distanceMax sourceRate
    extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  obtain ⟨allRatio, allMinimum, allFactory⟩ := alls extent magnitudeMax distanceMax sourceRate
    extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  let ratioMin := max costRatio (max addRatio allRatio)
  refine ⟨ratioMin, ((le_max_left _ _).trans costMinimum).trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant referenceNonnegative
    referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError boundaryOne timingErrorNonnegative ratioSeparation
  filter_upwards [costFactory scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity
      ((le_max_left _ _).trans ratioLarge) alphaPositive alphaSmall ratioPower referenceConstant referenceNonnegative referenceAmplitude
      threshold (thresholdBound.trans (min_le_left _ _)) orbit sectionTime boundaryConstant tolerance timingError boundaryOne
      toleranceChosenPositive (min_le_left _ _) timingErrorNonnegative ratioSeparation,
    addFactory scales scaleRoot ((le_max_left _ _).trans ((le_max_right _ _).trans rootLarge)) amplitudeIdentity
      ((le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge)) alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans ((min_le_right _ _).trans (min_le_left _ _)))
      orbit sectionTime boundaryConstant chartConstant tolerance timingError boundaryOne (zero_le_one.trans chartOne)
      toleranceChosenPositive.le (min_le_right _ _) timingErrorNonnegative ratioSeparation,
    allFactory scales scaleRoot ((le_max_right _ _).trans ((le_max_right _ _).trans rootLarge)) amplitudeIdentity
      ((le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge)) alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans ((min_le_right _ _).trans (min_le_right _ _)))
      orbit sectionTime boundaryConstant (1 / 32) timingError boundaryOne (by norm_num) timingErrorNonnegative ratioSeparation]
    with frequency costEstimate addEstimate allEstimate
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal entry initialDistance direction entries extents
    magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
    finish finishInside radialSmall targetSmall followerSmall sourceRates suppliedLift suppliedContinuous suppliedInitial suppliedPolar
    shapeProfile endpointBound
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
  let origin := entry ⟨index.val + 1, nonterminal⟩
  let state := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift index time + raw time
  let additive := fun time => tolerance * (moment time + center time + shape time) +
    stableConstant * omega * epsilon * (center time + raw time) +
    stableConstant * epsilon * ∑ patch : Fin 4, foreign patch time +
    stableConstant * (length / centerRadius) * (changed.strain * center time + difference time) +
    stableConstant * indexedReferenceSize * ‖leading time‖ + stableConstant * omega * indexedReferenceSize * dilation time
  let allForeign := prepared.selectedForeignForcing (Finset.univ.erase index) index
  have rawInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have sizeInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).finiteCoordinateSize = prepared.finiteCoordinateSize := rfl
  have selectedInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).selectedForeignForcing = prepared.selectedForeignForcing := rfl
  have costData := costEstimate count phase dipoleAngle (prepared.enlargeCap costCapBound) path index nonterminal
    entry initialDistance direction entries extents magnitude
    (by simpa only [rawInvariant, centeredInvariant] using profiles) magnitudeUpper distanceUpper domains actualTime timeIdentity
    nearestTiming sourceTiming timeOrder finish finishInside radialSmall
    (fun time inside => (targetSmall time inside).trans (min_le_left _ _))
    (fun receiver below time inside => (followerSmall receiver below time inside).trans (min_le_left _ _))
    sourceRates suppliedLift suppliedContinuous suppliedInitial suppliedPolar shapeProfile endpointBound
  dsimp only at costData
  simp only [rawInvariant, centeredInvariant, sizeInvariant, selectedInvariant] at costData
  obtain ⟨payload, _, _, _, _, _, stateProfile, _, _, costSmall, _⟩ := costData
  obtain ⟨_, _, _, _, _, _, _, growthPositive, relativeContinuous, leadingContinuous, _, _, _, _, histories, _⟩ := payload.1.1
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) := relativeContinuous.fst.abs.add relativeContinuous.snd.abs
  have initialQ := (histories 0 ⟨le_rfl, finishInside.1⟩).2.1
  have initialP := (histories 0 ⟨le_rfl, finishInside.1⟩).2.2.1
  have shapeInitial : shape 0 = 0 := by
    have qZero : (relative 0).1 = 0 := by simpa only [mul_zero, neg_zero, Real.exp_zero, one_mul,
      intervalIntegral.integral_same, zero_add] using initialQ
    have pZero : (relative 0).2 = 0 := by simpa only [intervalIntegral.integral_same] using initialP
    simp only [shape, qZero, pZero, abs_zero, zero_add]
  have currentSmall (receiver : Fin count) (below : receiver.val ≤ index.val) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape prepared.trajectory.movingFamily.patchMotion time receiver| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time receiver| ≤ radius := by
    rcases lt_or_eq_of_le below with strict | equal
    · exact followerSmall receiver strict time inside
    · have same : receiver = index := Fin.ext equal
      subst receiver
      exact targetSmall time inside
  have addData := addEstimate count phase dipoleAngle (prepared.enlargeCap addCapBound) path index nonterminal
    entry initialDistance direction entries extents magnitude
    (by simpa only [rawInvariant, centeredInvariant] using profiles) magnitudeUpper distanceUpper domains actualTime timeIdentity
    nearestTiming sourceTiming timeOrder finish finishInside radialSmall
    (fun receiver below time inside => (currentSmall receiver below time inside).trans ((min_le_right _ _).trans (min_le_left _ _)))
    suppliedLift suppliedContinuous suppliedInitial suppliedPolar sourceRates
  dsimp only at addData
  simp only [rawInvariant, centeredInvariant, sizeInvariant, selectedInvariant] at addData
  obtain ⟨_, _, _, _, additiveI, stateI, additiveBound⟩ := addData
  have allData := allEstimate count phase dipoleAngle (prepared.enlargeCap allCapBound) path index nonterminal
    entry initialDistance direction entries extents magnitude
    (by simpa only [rawInvariant, centeredInvariant] using profiles) magnitudeUpper distanceUpper domains actualTime timeIdentity
    nearestTiming sourceTiming timeOrder finish finishInside radialSmall
    (fun time inside => (targetSmall time inside).trans ((min_le_right _ _).trans (min_le_right _ _)))
    (fun receiver below time inside => (followerSmall receiver below time inside).trans ((min_le_right _ _).trans (min_le_right _ _)))
    sourceRates
  dsimp only at allData
  simp only [rawInvariant, centeredInvariant, selectedInvariant] at allData
  obtain ⟨_, shapeI, allI, literalBound, allBound⟩ := allData
  have finishOne : finish ≤ 1 := finishInside.2.trans path.stopBound
  have seedNonnegative : 0 ≤ changed.seed (index.val + 1) := by dsimp only [Scales.seed]; positivity
  have shapeAction := intervalIntegral.integral_exp_neg_mul_le_of_same_rate_majorant finishInside.1 shapeI shapeProfile
  have shapeReduced : (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * shape time) ≤
      profileMagnitude * changed.seed (index.val + 1) * Real.exp (-growth * origin) := by
    apply shapeAction.trans
    convert mul_le_mul_of_nonneg_right finishOne
      (mul_nonneg (mul_nonneg (zero_le_one.trans magnitudeOne) seedNonnegative) (Real.exp_pos (-growth * origin)).le) using 1 <;> ring
  have leadingDominance (time : ℝ) (inside : time ∈ Icc 0 finish) : ‖leading time‖ ≤ allForeign time := by
    have locationPositive := changed.location_pos (index.val + 1)
    have scalar (first second third fourth fifth : ℝ) (secondNonnegative : 0 ≤ second)
        (thirdNonnegative : 0 ≤ third) (fourthNonnegative : 0 ≤ fourth) (fifthNonnegative : 0 ≤ fifth) :
        first ≤ first + second + third + fourth + fifth := by linarith only [secondNonnegative, thirdNonnegative, fourthNonnegative, fifthNonnegative]
    have firstBound : ‖leading time‖ ≤ prepared.finiteCoordinateForeignForcing index time := by
      dsimp only [CascadeSourcePreparedPair.finiteCoordinateForeignForcing]
      rw [← prepared.referenceIdentity]
      apply scalar <;> positivity
    exact (firstBound.trans (le_add_of_nonneg_right (prepared.physicalForeignSourceForcing_nonneg index time))).trans (literalBound time inside)
  have exponential : Continuous (fun time : ℝ => Real.exp (-growth * time)) := by fun_prop
  have leadingI := (exponential.continuousOn.mul leadingContinuous.norm).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have leadingBound : (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * ‖leading time‖) ≤
      ((1 / 32 : ℝ) * profileMagnitude + leadingMagnitude) * changed.seed (index.val + 1) * Real.exp (-growth * origin) := by
    have comparison := intervalIntegral.integral_mono_on finishInside.1 leadingI allI
      (fun time inside => mul_le_mul_of_nonneg_left (leadingDominance time inside) (Real.exp_pos _).le)
    have reduced := allBound.trans (add_le_add_right (mul_le_mul_of_nonneg_left shapeReduced (by norm_num : (0 : ℝ) ≤ 1 / 32)) _)
    exact (comparison.trans reduced).trans_eq (by ring)
  have driveIdentity (time : ℝ) (_inside : time ∈ Icc 0 finish) : drive time = ‖leading time‖ + additive time := by
    dsimp only [drive, forcing, additive]
    ring
  have driveBound := General.weighted_drive_bound_of_state_profile finishInside.1 finishOne seedNonnegative
    (zero_le_one.trans magnitudeOne) (zero_le_one.trans profileOne) (zero_le_one.trans costOne) accuracyPositive.le
    stateI leadingI additiveI driveIdentity stateProfile leadingBound additiveBound
  have accuracyProfile : accuracy * profileConstant ≤ 1 / 64 := by
    have identity : accuracy * profileConstant = profileConstant / (64 * (1 + profileConstant)) := by
      dsimp only [accuracy]
      ring
    rw [identity]
    apply (div_le_iff₀ (by positivity : 0 < 64 * (1 + profileConstant))).mpr
    linarith only [profileOne]
  have feedbackBound : 4 * ((1 / 32 : ℝ) + 2 * accuracy * profileConstant) ≤ 1 / 4 := by linarith only [accuracyProfile]
  have response := (payload.1.2.2.2 finish ⟨finishInside.1, le_rfl⟩).2.2
  have smallAction := General.exponential_profile_le_of_small_action (zero_lt_one.trans_le stableOne)
    (show 0 ≤ (((1 / 32 : ℝ) + 2 * accuracy * profileConstant) * profileMagnitude + base) * changed.seed (index.val + 1) by positivity)
    costSmall.le response (by
      convert driveBound using 1
      dsimp only [base]
      ring)
  refine ⟨shapeContinuous, shapeInitial, smallAction.trans ?_⟩
  have scalarBound : 4 * (((1 / 32 : ℝ) + 2 * accuracy * profileConstant) * profileMagnitude + base) ≤ profileMagnitude / 2 := by
    have scaled := mul_le_mul_of_nonneg_right feedbackBound (zero_le_one.trans magnitudeOne)
    dsimp only [profileMagnitude] at scaled ⊢
    nlinarith only [scaled]
  convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right scalarBound seedNonnegative)
    (Real.exp_pos (growth * (finish - origin))).le using 1
  ring

end EulerNonuniqueness.Paper

