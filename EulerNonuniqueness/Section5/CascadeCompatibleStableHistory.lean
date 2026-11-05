import EulerNonuniqueness.Section5.CascadeCompatibleStableStrainRemainder
import EulerNonuniqueness.Section5.CascadeDomainAdditiveSeedSmall
import EulerNonuniqueness.Section5.CascadeSaddleOriginalDuhamel
import EulerNonuniqueness.Section5.CascadeLeadingStrainContinuity
import EulerNonuniqueness.Section1.UniformIntegratedReferenceIndexBudget
import EulerNonuniqueness.General.StableHistoryFeedbackAbsorption
import EulerNonuniqueness.General.TwoRateExponentialResponse

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem exists_uniform_actual_compatible_stable_history
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0)
    (certificateOrbit : SeparatingOrbit) (certificateNormalized : IsNormalizedSeparatingOrbit certificateOrbit)
    (certificateCompatible : ∀ᶠ time : ℝ in atBot,
      orbitStableShape certificateOrbit time = graph (orbitUnstableShape certificateOrbit time)) :
    ∃ chartConstant ≥ (1 : ℝ), ∃ pointConstant ≥ (1 : ℝ),
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ rootMin ≥ (8 : ℝ),
    ∃ stableConstant ≥ (1 : ℝ),
    ∀ currentStateMagnitude ≥ (0 : ℝ), ∃ endpoint > (0 : ℝ), endpoint ≤ 1 ∧
    endpoint ≤ 1 / (64 * pointConstant * (1 + currentStateMagnitude)) ∧
    ∀ precision > (0 : ℝ), ∃ tolerance > (0 : ℝ), tolerance ≤ 1 ∧
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
    let relative := fun time => referenceStraightenedShape motion graph coordinate receiver time -
      referenceStraightenedShape prepared.reference graph coordinate receiver time
    let shape := fun time => |(relative time).1| + |(relative time).2|
    let length := changed.length (receiver.val + 1)
    let omega := changed.omega (receiver.val + 1)
    let dilation := fun time => |diagonalDifference motion time receiver -
      diagonalDifference prepared.reference time receiver| / length ^ 2
    let referenceSize := chartConstant * referenceConstant *
      ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
    let leading := fun time => quadrupoleRelativeLeadingStrain changed motion prepared.reference time receiver
    let remainder := relativeStraightenedSaddleStrainRemainder changed
      (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate receiver
    let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
    let ownRadius := factor / 39321600 * length
    let epsilon := changed.radius (receiver.val + 1) ^ 2 / length ^ 2
    let difference := fun time => ∑' power : ℕ,
      ‖quadrupoleExteriorCoefficient changed motion receiver time macroRadius power -
        quadrupoleExteriorCoefficient changed prepared.reference receiver time macroRadius power‖
    let ownForcing := fun time => ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid motion current receiver patch) ownRadius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch)
            ownRadius (power + 1) time‖
    let additive := fun time => tolerance *
        (‖relativeNormalizedFirstMoment changed motion prepared.reference receiver time‖ +
          prepared.rawSourceCenteredState time receiver + shape time) +
      stableConstant * omega * epsilon * (prepared.rawSourceCenteredState time receiver +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch) +
      stableConstant * epsilon * ownForcing time +
      stableConstant * (length / macroRadius) *
        (changed.strain * prepared.rawSourceCenteredState time receiver + difference time) +
      stableConstant * referenceSize * ‖leading time‖ +
      stableConstant * omega * referenceSize * dilation time
    let coefficient := fun time => pointConstant * omega * (shape time + dilation time + referenceSize)
    ContinuousOn relative (Icc 0 finish) ∧ ContinuousOn leading (Icc 0 finish) ∧
    ContinuousOn remainder (Icc 0 finish) ∧ ContinuousOn coefficient (Icc 0 finish) ∧
    ContinuousOn additive (Icc 0 finish) ∧ ContinuousOn stateBudget (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * additive time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * stateBudget time) volume 0 finish ∧
    Real.exp (weight * origin) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * additive time) ≤
        precision * changed.seed (receiver.val + 1) ∧
    (∀ time ∈ Icc 0 finish, coefficient time ≤ weight / 2) ∧
    (∀ time ∈ Icc 0 finish,
      |(relative time).2| ≤ ∫ current in (0 : ℝ)..time,
        Real.exp (-(weight / 2) * (time - current)) *
          (|(leading current).2| + pointConstant * omega * referenceSize *
            (shape current + dilation current) + additive current)) ∧
    ∀ time ∈ Icc 0 finish,
      |(relative time).2| ≤ (∫ current in (0 : ℝ)..time,
        Real.exp (-(weight / 2) * (time - current)) * |(leading current).2|) + precision := by
  have graphSmooth : ContDiffAt ℝ 2 graph 0 := graphAnalytic.contDiffAt
  obtain ⟨chartConstant, chartOne, pointConstant, pointOne, pointThreshold, pointThresholdPositive,
    pointThresholdEighth, pointRadius, pointPositive, pointQuarter, strainCap, strainCapPositive, strains⟩ :=
    exists_uniform_actual_compatible_stable_strain_remainder graphAnalytic coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
      certificateOrbit certificateNormalized certificateCompatible
  obtain ⟨additiveThreshold, additiveThresholdPositive, additiveThresholdEighth, additiveCap, additiveCapPositive,
    coarseConstant, _, incomingConstant, _, outgoingConstant, _, commonIncoming, _, commonOutgoing, _,
    fullCommonIncoming, _, fullCommonOutgoing, _, fullSharpIncoming, _, fullSharpOutgoing, _,
    toleranceControl, _, additives⟩ :=
    exists_uniform_actual_domain_additive_seed_small graphAnalytic coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨duhamelRadius, duhamelPositive, _, duhamel⟩ :=
    exists_uniform_cascade_saddle_original_duhamel graphSmooth coordinateSmooth
  obtain ⟨regularRadius, regularPositive, _, regular⟩ :=
    exists_uniform_cascade_paired_chart_regularity graphSmooth coordinateSmooth
  let thresholdMax := min additiveThreshold pointThreshold
  let rawCap := min additiveCap strainCap
  have additiveCapBound : rawCap ≤ additiveCap := min_le_left _ _
  have strainCapBound : rawCap ≤ strainCap := min_le_right _ _
  refine ⟨chartConstant, chartOne, pointConstant, pointOne, thresholdMax,
    lt_min additiveThresholdPositive pointThresholdPositive, (min_le_left _ _).trans additiveThresholdEighth,
    rawCap, lt_min additiveCapPositive strainCapPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨additiveRadius, additivePositive, additiveQuarter, responseE, _, fullFollower, _,
    rootMin, rootEight, additiveFactory⟩ := additives factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, strainFactory⟩ := strains factorPositive factorSmall
  let radius := min additiveRadius (min pointRadius (min (duhamelRadius / 2) (regularRadius / 2)))
  have radiusAdditive : radius ≤ additiveRadius := min_le_left _ _
  have radiusPoint : radius ≤ pointRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusDuhamel : radius < duhamelRadius := by
    have bound : radius ≤ duhamelRadius / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith only [bound, duhamelPositive]
  have radiusRegular : radius < regularRadius := by
    have bound : radius ≤ regularRadius / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith only [bound, regularPositive]
  refine ⟨radius, lt_min additivePositive (lt_min pointPositive
    (lt_min (half_pos duhamelPositive) (half_pos regularPositive))),
    radiusAdditive.trans additiveQuarter, rootMin, rootEight, stableConstant, stableOne, ?_⟩
  intro currentStateMagnitude currentNonnegative
  let endpoint := min 1 (1 / (64 * pointConstant * (1 + currentStateMagnitude)))
  have pointPositive' : 0 < pointConstant := zero_lt_one.trans_le pointOne
  have endpointPositive : 0 < endpoint := by dsimp only [endpoint]; positivity
  refine ⟨endpoint, endpointPositive, min_le_left _ _, min_le_right _ _, ?_⟩
  intro precision precisionPositive
  obtain ⟨toleranceMax, toleranceMaxPositive, _, additiveEstimates⟩ :=
    additiveFactory stableConstant (zero_le_one.trans stableOne) currentStateMagnitude currentNonnegative
      (precision / 2) (half_pos precisionPositive)
  let tolerance := min 1 toleranceMax
  have tolerancePositive : 0 < tolerance := lt_min zero_lt_one toleranceMaxPositive
  refine ⟨tolerance, tolerancePositive, min_le_left _ _, ?_⟩
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
  have referenceTolerancePositive : 0 < 1 / (64 * pointConstant) := by positivity
  have referenceAccuracyPositive : 0 < precision / (8 * pointConstant * (1 + currentStateMagnitude)) := by positivity
  filter_upwards [additiveScales scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdAdditive orbit sectionTime boundaryConstant
      chartConstant tolerance timingError boundaryOne (zero_le_one.trans chartOne) tolerancePositive.le
      (min_le_right _ _) timingErrorNonnegative ratioSeparation,
    strainFactory tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      rootOne boundaryOne thresholdPoint referenceNonnegative,
    scales.eventually_cascade_relative_leading_strain_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative
      (lt_min duhamelPositive regularPositive),
    scales.eventually_uniform_reference_index_rate_small ratioBound alphaPositive
      (mul_nonneg (zero_le_one.trans chartOne) referenceNonnegative) referenceTolerancePositive,
    scales.eventually_uniform_reference_index_rate_small ratioBound alphaPositive
      (mul_nonneg (zero_le_one.trans chartOne) referenceNonnegative) referenceAccuracyPositive,
    eventually_ge_atTop (1 : ℝ)]
    with frequency additiveEstimate strainEstimate leadingEstimate referenceSmall referenceRate referenceAccuracy frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal entry initialDistance direction
  dsimp only
  intro entries extents magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
    finish finishInside small suppliedLift suppliedContinuous suppliedInitial suppliedPolar rateBounds currentProfile exposure
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
  let feedback := fun time => pointConstant * omega * (shape time + dilation time + referenceSize)
  have radialSmall (time : ℝ) (inside : time ∈ Icc 0 finish) : |radialShape first time receiver| ≤ 1 / 2 := by
    rw [radialShape_eq_unstable_add_stable]
    exact (abs_add _ _).trans ((small receiver le_rfl time inside).trans
      (radiusAdditive.trans (additiveQuarter.trans (by norm_num))))
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
  obtain ⟨_, additiveNonnegative, additiveContinuous, stateContinuous, additiveI, stateI, additiveBound⟩ :=
    additiveEstimate count phase dipoleAngle (prepared.enlargeCap additiveCapBound) path receiver nonterminal
      entry initialDistance direction entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity
      nearestTiming sourceTiming timeOrder finish finishInside radialSmall
      (fun current below time inside => (small current below time inside).trans radiusAdditive)
      suppliedLift suppliedContinuous suppliedInitial suppliedPolar rateBounds additiveProfile
  dsimp only at additiveNonnegative additiveContinuous stateContinuous additiveI stateI additiveBound
  simp only [rawInvariant, centerInvariant, sizeInvariant] at additiveNonnegative additiveContinuous stateContinuous additiveI stateI additiveBound
  change ∀ time ∈ Icc 0 finish, 0 ≤ additive time at additiveNonnegative
  change ContinuousOn additive (Icc 0 finish) at additiveContinuous
  change IntervalIntegrable (fun time => Real.exp (-weight * time) * additive time) volume 0 finish at additiveI
  change Real.exp (weight * origin) *
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * additive time) ≤
      precision / 2 * changed.seed (receiver.val + 1) at additiveBound
  have additiveHalfBound := additiveBound
  have additiveBound := additiveHalfBound.trans (mul_le_mul_of_nonneg_right
    (show precision / 2 ≤ precision by linarith only [precisionPositive])
    (show 0 ≤ changed.seed (receiver.val + 1) by dsimp only [Scales.seed]; positivity))
  change ContinuousOn stateBudget (Icc 0 finish) at stateContinuous
  change IntervalIntegrable (fun time => Real.exp (-weight * time) * stateBudget time) volume 0 finish at stateI
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := lt_of_lt_of_le (by norm_num) ratioBound
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive
    (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _)
  have sqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
  have omegaWeight : omega ≤ weight / 2 := by dsimp only [weight]; nlinarith only [omegaPositive, sqrtOne]
  have weightPositive : 0 < weight := by dsimp only [weight]; positivity
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (motions side) time receiver| + |stableShape (motions side) time receiver| < min duhamelRadius regularRadius := by
    fin_cases side
    · exact (small receiver le_rfl time inside).trans_lt (lt_min radiusDuhamel radiusRegular)
    · have actual := referenceSmall prepared.toCascadeMaterialPreparedPair time
        ⟨inside.1, inside.2.trans (finishInside.2.trans path.stopBound)⟩ receiver
      change |unstableShape second time receiver| + |stableShape second time receiver| < min duhamelRadius regularRadius
      linarith only [actual, abs_nonneg (diagonalDifference second time receiver / length ^ 2 - 1)]
  have original := duhamel prepared.toCascadeMaterialPreparedPair path receiver nonterminal finish finishInside.1 finishInside.2
    (fun side time inside => (pairedSmall side time inside).trans_le (min_le_left _ _))
  have relativeContinuous := (regular prepared.toCascadeMaterialPreparedPair path receiver finish finishInside.2
    (fun side time inside => (pairedSmall side time inside).trans_le (min_le_right _ _))).1
  change ContinuousOn relative (Icc 0 finish) at relativeContinuous
  have leadingContinuous : ContinuousOn leading (Icc 0 finish) :=
    (leadingEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver).mono
      (fun _ inside => ⟨inside.1, inside.2.trans finishInside.2⟩)
  have remainderContinuous : ContinuousOn remainder (Icc 0 finish) := by
    apply (original.1.sub leadingContinuous).congr
    intro time _
    change remainder time = leading time + remainder time - leading time
    abel
  have centroids (side : Fin 2) (patch : Fin 4) : Continuous (fun time => patchCentroid (motions side) time receiver patch) := by
    fin_cases side
    · exact prepared.trajectory.movingFamily.patchCentroid_continuous receiver patch
    · simpa only [motions, cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] using
        prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous receiver patch
  have diagonalContinuous (side : Fin 2) : Continuous (fun time => diagonalDifference (motions side) time receiver) :=
    ((((centroids side 0).sub (centroids side 1)).div_const 2).norm.pow 2).sub
      ((((centroids side 2).sub (centroids side 3)).div_const 2).norm.pow 2)
  have dilationContinuous : ContinuousOn dilation (Icc 0 finish) :=
    (((diagonalContinuous 0).sub (diagonalContinuous 1)).abs.div_const (length ^ 2)).continuousOn
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) := relativeContinuous.fst.abs.add relativeContinuous.snd.abs
  have feedbackContinuous : ContinuousOn feedback (Icc 0 finish) :=
    continuousOn_const.mul ((shapeContinuous.add dilationContinuous).add continuousOn_const)
  have rateData := referenceRate (receiver.val + 1)
  have referenceNonnegative' : 0 ≤ referenceSize := by
    have actual := rateData.1
    change 0 ≤ omega * referenceSize at actual
    exact nonneg_of_mul_nonneg_right actual omegaPositive
  have referenceRateBound : pointConstant * referenceSize ≤ 1 / 64 := by
    have actual := rateData.2.le
    change omega * referenceSize ≤ 1 / (64 * pointConstant) at actual
    have small := (mul_le_mul_of_nonneg_right omegaOne referenceNonnegative')
    have scaled := mul_le_mul_of_nonneg_left (small.trans actual) pointPositive'.le
    have identity : pointConstant * (1 / (64 * pointConstant)) = 1 / 64 := by field_simp; ring
    simpa only [identity, one_mul] using scaled
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
  have exposureBound (time : ℝ) (inside : time ∈ Icc 0 finish) : stateBudget time ≤ currentStateMagnitude * endpoint := by
    have expBound : Real.exp (weight * (time - origin)) ≤ Real.exp (weight * (finish - origin)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 origin) weightPositive.le)
    have seedNonnegative : 0 ≤ changed.seed (receiver.val + 1) := (changed.seed_pos frequencyPositive ratioPositive _).le
    have bound := (currentProfile time inside).trans
      (mul_le_mul_of_nonneg_left expBound (mul_nonneg currentNonnegative seedNonnegative))
    have associated : stateBudget time ≤ currentStateMagnitude *
        (changed.seed (receiver.val + 1) * Real.exp (weight * (finish - origin))) := by
      simpa only [mul_assoc] using bound
    exact associated.trans (mul_le_mul_of_nonneg_left exposure currentNonnegative)
  have endpointCoefficient : pointConstant * currentStateMagnitude * endpoint ≤ 1 / 64 := by
    have bound := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (1 / (64 * pointConstant * (1 + currentStateMagnitude))))
      (by positivity : 0 ≤ 64 * pointConstant * (1 + currentStateMagnitude))
    have identity : (64 * pointConstant * (1 + currentStateMagnitude)) *
        (1 / (64 * pointConstant * (1 + currentStateMagnitude))) = 1 := by field_simp
    rw [identity] at bound
    have slack : 0 ≤ pointConstant * endpoint := mul_nonneg pointPositive'.le endpointPositive.le
    change 64 * pointConstant * (1 + currentStateMagnitude) * endpoint ≤ 1 at bound
    nlinarith only [bound, slack]
  have feedbackUpper (time : ℝ) (inside : time ∈ Icc 0 finish) : feedback time ≤ weight / 2 := by
    have sizes := stateDominates time
    have sizeBound : shape time + dilation time ≤ 2 * (currentStateMagnitude * endpoint) := by
      linarith only [sizes.1, sizes.2, exposureBound time inside]
    have scaled := mul_le_mul_of_nonneg_left sizeBound pointPositive'.le
    have coefficient : pointConstant * (shape time + dilation time + referenceSize) ≤ 1 := by
      nlinarith only [scaled, endpointCoefficient, referenceRateBound]
    have bounded := mul_le_mul_of_nonneg_left coefficient omegaPositive.le
    change pointConstant * omega * (shape time + dilation time + referenceSize) ≤ weight / 2
    have normalized : pointConstant * omega * (shape time + dilation time + referenceSize) ≤ omega := by
      simpa only [mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using bounded
    exact normalized.trans omegaWeight
  have remainderBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |(remainder time).2| ≤ feedback time * |(relative time).2| +
        (pointConstant * omega * referenceSize * (shape time + dilation time) + additive time) := by
    have actual := (strainEstimate count phase dipoleAngle (prepared.enlargeCap strainCapBound) path receiver nonterminal
      finish finishInside.1 finishInside.2
      (fun time inside => (small receiver le_rfl time inside).trans radiusPoint) time inside).2.2
    dsimp only at actual
    simp only [rawInvariant, centerInvariant] at actual
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at actual
    have extra : 0 ≤ stableConstant * omega * referenceSize * dilation time := by
      have stableNonnegative := zero_le_one.trans stableOne
      have dilationNonnegative : 0 ≤ dilation time := div_nonneg (abs_nonneg _) (sq_nonneg _)
      positivity
    have normalized : |(remainder time).2| ≤ pointConstant * |omega| *
      ((shape time + dilation time + referenceSize) * |(relative time).2| + referenceSize * (shape time + dilation time)) +
      (additive time - stableConstant * omega * referenceSize * dilation time) := by
      convert actual using 1
      dsimp only [additive, referenceSize, shape, relative, omega, epsilon, center, raw, moment,
        length, macroRadius, ownForcing, ownRadius, difference, leading, first, second, dilation]
      ring
    rw [abs_of_pos omegaPositive] at normalized
    dsimp only [feedback]
    nlinarith only [normalized, extra]
  have forcingContinuous : ContinuousOn (fun time =>
      pointConstant * omega * referenceSize * (shape time + dilation time) + additive time) (Icc 0 finish) :=
    (continuousOn_const.mul (shapeContinuous.add dilationContinuous)).add additiveContinuous
  have history := General.stable_original_history_feedback_bound finishInside.1 weightPositive.le
    relativeContinuous leadingContinuous remainderContinuous feedbackContinuous forcingContinuous
    feedbackUpper remainderBound original.2.2.1
  have referenceCoefficient : 2 * pointConstant * currentStateMagnitude * omega * referenceSize ≤ precision / 4 := by
    have actual := (referenceAccuracy (receiver.val + 1)).2.le
    change omega * referenceSize ≤ precision / (8 * pointConstant * (1 + currentStateMagnitude)) at actual
    have scaled := mul_le_mul_of_nonneg_left actual (by positivity : 0 ≤ 8 * pointConstant * (1 + currentStateMagnitude))
    have identity : (8 * pointConstant * (1 + currentStateMagnitude)) *
        (precision / (8 * pointConstant * (1 + currentStateMagnitude))) = precision := by field_simp
    rw [identity] at scaled
    have nonnegative : 0 ≤ pointConstant * omega * referenceSize := by positivity
    nlinarith only [scaled, nonnegative]
  let referenceDrive := fun time => pointConstant * omega * referenceSize * (shape time + dilation time)
  have referenceContinuous : ContinuousOn referenceDrive (Icc 0 finish) :=
    continuousOn_const.mul (shapeContinuous.add dilationContinuous)
  have stableAccuracy (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |(relative time).2| ≤ (∫ current in (0 : ℝ)..time,
        Real.exp (-(weight / 2) * (time - current)) * |(leading current).2|) + precision := by
    have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have seedNonnegative : 0 ≤ changed.seed (receiver.val + 1) := (changed.seed_pos frequencyPositive ratioPositive _).le
    have qBound : changed.seed (receiver.val + 1) * Real.exp (weight * (time - origin)) ≤ 1 := by
      have monotone := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 origin) weightPositive.le)) seedNonnegative
      exact monotone.trans (exposure.trans (min_le_left _ _))
    have weightedI (function : ℝ → ℝ) (continuous : ContinuousOn function (Icc 0 finish)) (rate : ℝ) :
        IntervalIntegrable (fun current => Real.exp (-rate * current) * function current) volume 0 time :=
      ((show Continuous (fun current : ℝ => Real.exp (-rate * current)) by fun_prop).continuousOn.mul
        (continuous.mono subset)).intervalIntegrable_of_Icc inside.1
    have majorized (current : ℝ) (member : current ∈ Icc 0 time) : referenceDrive current ≤
        (2 * pointConstant * currentStateMagnitude * omega * referenceSize * changed.seed (receiver.val + 1)) *
          Real.exp (weight * (current - origin)) := by
      have sizes := stateDominates current
      have profile := currentProfile current (subset member)
      change stateBudget current ≤ currentStateMagnitude * changed.seed (receiver.val + 1) *
        Real.exp (weight * (current - origin)) at profile
      have sizeBound : shape current + dilation current ≤ 2 *
          (currentStateMagnitude * changed.seed (receiver.val + 1) * Real.exp (weight * (current - origin))) := by
        linarith only [sizes.1, sizes.2, profile]
      have scaled := mul_le_mul_of_nonneg_left sizeBound (by positivity : 0 ≤ pointConstant * omega * referenceSize)
      dsimp only [referenceDrive]
      nlinarith only [scaled]
    have refResponse := intervalIntegral.exp_mul_integral_le_of_faster_exponential_majorant
      inside.1 (show -(weight / 2) < weight by linarith only [weightPositive])
      (show 0 ≤ 2 * pointConstant * currentStateMagnitude * omega * referenceSize * changed.seed (receiver.val + 1) by positivity)
      (weightedI referenceDrive referenceContinuous (-(weight / 2))) majorized
    have gapOne : 1 ≤ weight - -(weight / 2) := by linarith only [omegaOne, omegaWeight, weightPositive]
    have boundNonnegative : 0 ≤ 2 * pointConstant * currentStateMagnitude * omega * referenceSize * changed.seed (receiver.val + 1) := by positivity
    have coefficientBound := (div_le_self boundNonnegative gapOne).trans
      (mul_le_mul_of_nonneg_right referenceCoefficient seedNonnegative)
    have referenceSmall := refResponse.trans (mul_le_mul_of_nonneg_right coefficientBound (Real.exp_pos _).le)
    have referenceFinal : (∫ current in (0 : ℝ)..time,
        Real.exp (-(weight / 2) * (time - current)) * referenceDrive current) ≤ precision / 4 := by
      change EulerNonuniqueness.exponentialResponse (-(weight / 2)) referenceDrive time ≤ _ at referenceSmall
      rw [EulerNonuniqueness.exponentialResponse_eq_integral] at referenceSmall
      exact referenceSmall.trans (by nlinarith only [mul_le_mul_of_nonneg_left qBound (by positivity : 0 ≤ precision / 4)])
    have additivePrefixIntegral : (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * additive current) ≤
        ∫ current in (0 : ℝ)..finish, Real.exp (-weight * current) * additive current := by
      apply intervalIntegral.integral_mono_interval le_rfl inside.1 inside.2
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with current member
        exact mul_nonneg (Real.exp_pos _).le (additiveNonnegative current ⟨member.1.le, member.2⟩)
      · exact additiveI
    have addResponse := intervalIntegral.exp_mul_integral_weighted_mono_rate inside.1
      (show -(weight / 2) ≤ weight by linarith only [weightPositive])
      (weightedI additive additiveContinuous (-(weight / 2))) (weightedI additive additiveContinuous weight)
      (fun current member => additiveNonnegative current (subset member))
    have addPrefix := addResponse.trans (mul_le_mul_of_nonneg_left additivePrefixIntegral (Real.exp_pos _).le)
    have cancellation : Real.exp (weight * time) = Real.exp (weight * (time - origin)) * Real.exp (weight * origin) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [cancellation, mul_assoc] at addPrefix
    have addSmall := addPrefix.trans (mul_le_mul_of_nonneg_left additiveHalfBound (Real.exp_pos _).le)
    have additiveFinal : (∫ current in (0 : ℝ)..time,
        Real.exp (-(weight / 2) * (time - current)) * additive current) ≤ precision / 2 := by
      change EulerNonuniqueness.exponentialResponse (-(weight / 2)) additive time ≤ _ at addSmall
      rw [EulerNonuniqueness.exponentialResponse_eq_integral] at addSmall
      exact addSmall.trans (by nlinarith only [mul_le_mul_of_nonneg_left qBound (by positivity : 0 ≤ precision / 2)])
    have kernelI (function : ℝ → ℝ) (continuous : ContinuousOn function (Icc 0 finish)) :
        IntervalIntegrable (fun current => Real.exp (-(weight / 2) * (time - current)) * function current) volume 0 time :=
      ((show Continuous (fun current : ℝ => Real.exp (-(weight / 2) * (time - current))) by fun_prop).continuousOn.mul
        (continuous.mono subset)).intervalIntegrable_of_Icc inside.1
    have original : |(relative time).2| ≤ ∫ current in (0 : ℝ)..time,
        Real.exp (-(weight / 2) * (time - current)) *
          (|(leading current).2| + referenceDrive current + additive current) := by
      simpa only [referenceDrive, add_assoc] using history time inside
    simp_rw [mul_add] at original
    rw [intervalIntegral.integral_add ((kernelI _ leadingContinuous.snd.abs).add (kernelI _ referenceContinuous))
      (kernelI _ additiveContinuous), intervalIntegral.integral_add (kernelI _ leadingContinuous.snd.abs)
      (kernelI _ referenceContinuous)] at original
    linarith only [original, referenceFinal, additiveFinal, precisionPositive]
  refine ⟨relativeContinuous, leadingContinuous, remainderContinuous, feedbackContinuous, additiveContinuous,
    stateContinuous, additiveI, stateI, additiveBound, feedbackUpper, ?_, stableAccuracy⟩
  change ∀ time ∈ Icc 0 finish, |(relative time).2| ≤ ∫ current in (0 : ℝ)..time,
    Real.exp (-(weight / 2) * (time - current)) *
      (|(leading current).2| + pointConstant * omega * referenceSize * (shape current + dilation current) + additive current)
  simpa only [add_assoc] using history

end EulerNonuniqueness.Paper
