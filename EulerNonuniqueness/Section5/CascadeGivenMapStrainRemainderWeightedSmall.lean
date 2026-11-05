import EulerNonuniqueness.Section5.CascadeDomainAdditiveSeedSmall
import EulerNonuniqueness.Section5.CascadeGivenMapPointRemainderWeightedSmall
import EulerNonuniqueness.Section5.CascadeGivenMapCanonicalStrainForcing
import EulerNonuniqueness.Section5.CascadeSaddleOriginalDuhamel
import EulerNonuniqueness.Section5.CascadeLeadingStrainContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_actual_given_map_strain_remainder_weighted_small
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ rootMin ≥ (8 : ℝ),
    ∀ currentStateMagnitude ≥ (0 : ℝ), ∀ precision > (0 : ℝ),
    ∃ endpoint > (0 : ℝ),
    ∀ extent magnitudeMax distanceMax coefficient : ℝ,
    1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < coefficient →
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
    let stateBudget := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
    let origin := entry ⟨receiver.val + 1, nonterminal⟩
    (∀ time ∈ Icc 0 finish, stateBudget time ≤ currentStateMagnitude * changed.seed (receiver.val + 1) *
      Real.exp (weight * (time - origin))) →
    changed.seed (receiver.val + 1) * Real.exp (weight * (finish - origin)) ≤ endpoint →
    let remainder := relativeStraightenedSaddleStrainRemainder changed
      (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate receiver
    ContinuousOn remainder (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖remainder time‖) volume 0 finish ∧
    Real.exp (weight * origin) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖remainder time‖) ≤
        precision * changed.seed (receiver.val + 1) := by
  have graphSmooth : ContDiffAt ℝ 2 graph 0 := graphAnalytic.contDiffAt
  obtain ⟨chartConstant, chartOne, pointConstant, _, pointThreshold, pointThresholdPositive,
    pointThresholdEighth, pointRadius, pointPositive, _, points⟩ :=
    exists_uniform_actual_given_map_point_remainder_weighted_small graphSmooth coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨additiveThreshold, additiveThresholdPositive, additiveThresholdEighth, additiveCap, additiveCapPositive,
    coarseConstant, _, incomingConstant, _, outgoingConstant, _, commonIncoming, _, commonOutgoing, _,
    fullCommonIncoming, _, fullCommonOutgoing, _, fullSharpIncoming, _, fullSharpOutgoing, _,
    toleranceControl, _, additives⟩ :=
    exists_uniform_actual_domain_additive_seed_small graphAnalytic coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨canonicalRadius, canonicalPositive, _, canonicalCap, canonicalCapPositive, canonicals⟩ :=
    exists_uniform_actual_given_map_canonical_strain_forcing graphSmooth coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨duhamelRadius, duhamelPositive, _, duhamel⟩ :=
    exists_uniform_cascade_saddle_original_duhamel graphSmooth coordinateSmooth
  let thresholdMax := min additiveThreshold pointThreshold
  let rawCap := min additiveCap canonicalCap
  have additiveCapBound : rawCap ≤ additiveCap := min_le_left _ _
  have canonicalCapBound : rawCap ≤ canonicalCap := min_le_right _ _
  refine ⟨thresholdMax, lt_min additiveThresholdPositive pointThresholdPositive,
    (min_le_left _ _).trans additiveThresholdEighth, rawCap,
    lt_min additiveCapPositive canonicalCapPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨additiveRadius, additivePositive, additiveQuarter, responseE, _, fullFollower, _,
    rootMin, rootEight, additiveFactory⟩ := additives factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, canonicalFactory⟩ := canonicals factorPositive factorSmall
  let radius := min additiveRadius (min canonicalRadius (min pointRadius (duhamelRadius / 2)))
  have radiusPositive : 0 < radius :=
    lt_min additivePositive (lt_min canonicalPositive (lt_min pointPositive (half_pos duhamelPositive)))
  have radiusAdditive : radius ≤ additiveRadius := min_le_left _ _
  have radiusCanonical : radius ≤ canonicalRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusPoint : radius ≤ pointRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have radiusDuhamel : radius < duhamelRadius := by
    have bound : radius ≤ duhamelRadius / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith only [bound, duhamelPositive]
  refine ⟨radius, radiusPositive, radiusAdditive.trans additiveQuarter, rootMin, rootEight, ?_⟩
  intro currentStateMagnitude currentNonnegative precision precisionPositive
  have halfPositive : 0 < precision / 2 := half_pos precisionPositive
  obtain ⟨endpoint, endpointPositive, pointFactory⟩ :=
    points currentStateMagnitude currentStateMagnitude (precision / 2) currentNonnegative currentNonnegative halfPositive
  obtain ⟨toleranceMax, toleranceMaxPositive, _, additiveEstimates⟩ :=
    additiveFactory stableConstant (zero_le_one.trans stableOne) currentStateMagnitude currentNonnegative
      (precision / 2) halfPositive
  let tolerance := min 1 toleranceMax
  have tolerancePositive : 0 < tolerance := lt_min zero_lt_one toleranceMaxPositive
  refine ⟨endpoint, endpointPositive, ?_⟩
  intro extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  obtain ⟨ratioMin, ratioTwo, additiveScales⟩ :=
    additiveEstimates extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  refine ⟨ratioMin, ratioTwo, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime
    boundaryConstant timingError boundaryOne timingErrorNonnegative ratioSeparation
  have ratioBound : 2 ≤ scales.ratio := ratioTwo.trans ratioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdAdditive : threshold ≤ additiveThreshold := thresholdBound.trans (min_le_left _ _)
  have thresholdPoint : threshold ≤ pointThreshold := thresholdBound.trans (min_le_right _ _)
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdAdditive.trans additiveThresholdEighth
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  filter_upwards [additiveScales scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdAdditive orbit sectionTime boundaryConstant
      chartConstant tolerance timingError boundaryOne (zero_le_one.trans chartOne) tolerancePositive.le
      (min_le_right _ _) timingErrorNonnegative ratioSeparation,
    canonicalFactory chartConstant chartOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive
      orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative,
    pointFactory scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) factorPositive factorEighth thresholdPoint referenceNonnegative,
    scales.eventually_cascade_relative_leading_strain_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative duhamelPositive,
    eventually_ge_atTop (1 : ℝ)]
    with frequency additiveEstimate canonicalEstimate pointEstimate leadingEstimate referenceSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal entry initialDistance direction
  dsimp only
  intro entries extents magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
    finish finishInside radialSmall small suppliedLift suppliedContinuous suppliedInitial suppliedPolar rateBounds currentProfile exposure
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let motions := cascadePairedMotion prepared.toCascadeMaterialPreparedPair
  let omega := changed.omega (receiver.val + 1)
  let weight := 2 * Real.sqrt 2 * omega
  let length := changed.length (receiver.val + 1)
  let origin := entry ⟨receiver.val + 1, nonterminal⟩
  let relative := fun time => referenceStraightenedShape first graph coordinate receiver time -
    referenceStraightenedShape second graph coordinate receiver time
  let shape := fun time => |(relative time).1| + |(relative time).2|
  let dilation := fun time => |diagonalDifference first time receiver - diagonalDifference second time receiver| / length ^ 2
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
  let stateBudget := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time + raw time
  let pointR := relativeStraightenedSaddlePointRemainder changed motions graph coordinate receiver
  let remainder := relativeStraightenedSaddleStrainRemainder changed motions graph coordinate receiver
  let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time receiver
  let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
  let ownRadius := factor / 39321600 * length
  let epsilon := changed.radius (receiver.val + 1) ^ 2 / length ^ 2
  let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  let moment := fun time => ‖relativeNormalizedFirstMoment changed first second receiver time‖
  let center := fun time => prepared.rawSourceCenteredState time receiver
  let difference := fun time => ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first receiver time macroRadius power -
    quadrupoleExteriorCoefficient changed second receiver time macroRadius power‖
  let ownForcing := fun time => ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        (fun current => patchCentroid first current receiver patch) ownRadius (power + 1) time -
      prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch)
          ownRadius (power + 1) time‖
  let additive := fun time => tolerance * (moment time + center time + shape time) +
    stableConstant * omega * epsilon * (center time + raw time) + stableConstant * epsilon * ownForcing time +
    stableConstant * (length / macroRadius) * (changed.strain * center time + difference time) +
    stableConstant * referenceSize * ‖leading time‖ + stableConstant * omega * referenceSize * dilation time
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
  have sourceProfiles := profiles
  rw [← rawInvariant additiveCapBound, ← centerInvariant additiveCapBound] at sourceProfiles
  have additiveProfile := currentProfile
  rw [← rawInvariant additiveCapBound, ← sizeInvariant additiveCapBound] at additiveProfile
  obtain ⟨_, _, additiveContinuous, _, additiveI, _, additiveBound⟩ :=
    additiveEstimate count phase dipoleAngle (prepared.enlargeCap additiveCapBound) path receiver nonterminal
      entry initialDistance direction entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity
      nearestTiming sourceTiming timeOrder finish finishInside radialSmall
      (fun current below time inside => (small current below time inside).trans radiusAdditive)
      suppliedLift suppliedContinuous suppliedInitial suppliedPolar rateBounds additiveProfile
  dsimp only at additiveContinuous additiveI additiveBound
  simp only [rawInvariant, centerInvariant, sizeInvariant] at additiveContinuous additiveI additiveBound
  change ContinuousOn additive (Icc 0 finish) at additiveContinuous
  change IntervalIntegrable (fun time => Real.exp (-weight * time) * additive time) volume 0 finish at additiveI
  change Real.exp (weight * origin) *
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * additive time) ≤
      precision / 2 * changed.seed (receiver.val + 1) at additiveBound
  have locationPositive := changed.location_pos (receiver.val + 1)
  have stateDominates (time : ℝ) : shape time ≤ stateBudget time ∧ dilation time ≤ stateBudget time := by
    have rawNonnegative : 0 ≤ raw time := by
      apply Finset.sum_nonneg
      intro patch _
      dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    have phaseNonnegative := abs_nonneg (relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift motions receiver time)
    have momentNonnegative := norm_nonneg (relativeNormalizedFirstMoment changed first second receiver time)
    have translationNonnegative := div_nonneg (norm_nonneg (quadrupoleCenter first time receiver -
      quadrupoleCenter second time receiver)) locationPositive.le
    have dilationNonnegative : 0 ≤ dilation time := div_nonneg (abs_nonneg _) (sq_nonneg _)
    have shapeNonnegative : 0 ≤ shape time := add_nonneg (abs_nonneg _) (abs_nonneg _)
    change shape time ≤ shape time + dilation time +
      |relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift motions receiver time| +
      ‖relativeNormalizedFirstMoment changed first second receiver time‖ +
      ‖quadrupoleCenter first time receiver - quadrupoleCenter second time receiver‖ / changed.location (receiver.val + 1) + raw time ∧
      dilation time ≤ shape time + dilation time +
      |relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift motions receiver time| +
      ‖relativeNormalizedFirstMoment changed first second receiver time‖ +
      ‖quadrupoleCenter first time receiver - quadrupoleCenter second time receiver‖ / changed.location (receiver.val + 1) + raw time
    have rest : shape time + dilation time ≤ shape time + dilation time +
        |relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift motions receiver time| +
        ‖relativeNormalizedFirstMoment changed first second receiver time‖ +
        ‖quadrupoleCenter first time receiver - quadrupoleCenter second time receiver‖ /
          changed.location (receiver.val + 1) + raw time :=
      (((le_add_of_nonneg_right phaseNonnegative).trans (le_add_of_nonneg_right momentNonnegative)).trans
        (le_add_of_nonneg_right translationNonnegative)).trans (le_add_of_nonneg_right rawNonnegative)
    exact ⟨(le_add_of_nonneg_right dilationNonnegative).trans rest,
      (le_add_of_nonneg_left shapeNonnegative).trans rest⟩
  obtain ⟨_, pointI, pointBound⟩ := pointEstimate prepared.toCascadeMaterialPreparedPair path receiver nonterminal finish finishInside.1
    finishInside.2 (fun time inside => (small receiver le_rfl time inside).trans radiusPoint) origin
    (fun time inside => (stateDominates time).1.trans (currentProfile time inside))
    (fun time inside => (stateDominates time).2.trans (currentProfile time inside)) exposure
  change IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖pointR time‖) volume 0 finish at pointI
  change Real.exp (weight * origin) *
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖pointR time‖) ≤
      precision / 2 * changed.seed (receiver.val + 1) at pointBound
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (motions side) time receiver| + |stableShape (motions side) time receiver| < duhamelRadius := by
    fin_cases side
    · exact (small receiver le_rfl time inside).trans_lt radiusDuhamel
    · have actual := referenceSmall prepared.toCascadeMaterialPreparedPair time
        ⟨inside.1, inside.2.trans (finishInside.2.trans path.stopBound)⟩ receiver
      change |unstableShape second time receiver| + |stableShape second time receiver| < duhamelRadius
      linarith only [actual, abs_nonneg (diagonalDifference second time receiver / length ^ 2 - 1)]
  have original := duhamel prepared.toCascadeMaterialPreparedPair path receiver nonterminal finish finishInside.1 finishInside.2 pairedSmall
  have leadingContinuous : ContinuousOn leading (Icc 0 finish) :=
    (leadingEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver).mono
      (fun _ inside => ⟨inside.1, inside.2.trans finishInside.2⟩)
  have remainderContinuous : ContinuousOn remainder (Icc 0 finish) := by
    apply (original.1.sub leadingContinuous).congr
    intro time _
    change remainder time = leading time + remainder time - leading time
    abel
  have exponential : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have remainderI := (exponential.continuousOn.mul remainderContinuous.norm).intervalIntegrable_of_Icc
    (μ := volume) finishInside.1
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := lt_of_lt_of_le (by norm_num) ratioBound
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have referenceNonnegative' : 0 ≤ referenceSize := by dsimp only [referenceSize]; positivity
  have remainderBound (time : ℝ) (inside : time ∈ Icc 0 finish) : ‖remainder time‖ ≤ ‖pointR time‖ + additive time := by
    have canonical := (canonicalEstimate count phase dipoleAngle (prepared.enlargeCap canonicalCapBound) path receiver nonterminal
      finish finishInside.1 finishInside.2
      (fun time inside => (small receiver le_rfl time inside).trans radiusCanonical) time inside).2.2
    dsimp only at canonical
    simp only [rawInvariant, centerInvariant] at canonical
    have extraNonnegative : 0 ≤ stableConstant * omega * referenceSize * dilation time := by
      have stableNonnegative := zero_le_one.trans stableOne
      have dilationNonnegative : 0 ≤ dilation time := div_nonneg (abs_nonneg _) (sq_nonneg _)
      positivity
    have forcingBound :
        ‖referenceStraightenedForcing changed first graph coordinate receiver time -
          referenceStraightenedForcing changed second graph coordinate receiver time - leading time‖ ≤ additive time := by
      exact canonical.trans (le_add_of_nonneg_right extraNonnegative)
    exact (norm_add_le (pointR time) _).trans (add_le_add_left forcingBound ‖pointR time‖)
  have integralBound := intervalIntegral.integral_mono_on (μ := volume) finishInside.1 remainderI (pointI.add additiveI)
    (fun time inside => by
      simpa only [mul_add] using mul_le_mul_of_nonneg_left (remainderBound time inside) (Real.exp_pos (-weight * time)).le)
  rw [intervalIntegral.integral_add pointI additiveI] at integralBound
  have normalized := mul_le_mul_of_nonneg_left integralBound (Real.exp_pos (weight * origin)).le
  refine ⟨remainderContinuous, remainderI, ?_⟩
  change Real.exp (weight * origin) * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖remainder time‖) ≤
    precision * changed.seed (receiver.val + 1)
  linarith only [normalized, pointBound, additiveBound]

end EulerNonuniqueness.Paper

