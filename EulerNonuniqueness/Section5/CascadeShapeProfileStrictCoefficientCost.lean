import EulerNonuniqueness.Section5.CascadeProfileAccumulatedCoefficientCost
import EulerNonuniqueness.Section5.CascadeGivenMapShapeProfileEndpoint
import EulerNonuniqueness.Section5.CascadeMixedAllForeignClosedWeightedForcing
import EulerNonuniqueness.Section1.UniformIntegratedReferenceIndexBudget

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_shape_profile_strict_coefficient_cost :
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
      ∃ ratioMin ≥ max 2 (4 * followerConstant), ∃ rootMin ≥ (8 : ℝ),
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      ∀ shapeMagnitude sourceMagnitude actionTolerance : ℝ, 0 ≤ shapeMagnitude → 0 ≤ sourceMagnitude → 0 < actionTolerance →
      ∃ endpointSize > (0 : ℝ),
      ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
      ratioMin ≤ scales.ratio → 0 < scales.alpha → ∀ extent : ℝ, 1 ≤ extent →
      ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
      ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant tolerance : ℝ),
      1 ≤ boundaryConstant → 0 < tolerance → tolerance ≤ 1 →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ index : Fin count, index.val + 1 < count → ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ path.stop →
      ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
      let changed : Scales := {scales with frequency := frequency}
      let motion := prepared.trajectory.movingFamily.patchMotion
      (∀ source : Fin count, index.val < source.val →
        let length := changed.length (source.val + 1)
        0 ≤ entry source ∧ entry source ≤ terminal ∧ 512 ≤ initialDistance source ∧
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
      ∀ sourceRate : ℝ, 0 < sourceRate → ∀ magnitude : Fin count → ℝ,
      let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
        ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
        ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
      (∀ source : Fin count, index.val < source.val → 0 ≤ magnitude source ∧ ∀ time ∈ Icc 0 (entry source),
        sharpState source time ≤ magnitude source * Real.exp (sourceRate * changed.omega (source.val + 1) * (time - entry source))) →
  
      ∀ finish ∈ Icc 0 terminal,
      (∀ time ∈ Icc 0 finish, |radialShape motion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 finish, |unstableShape motion time index| + |stableShape motion time index| ≤ radius) →
      (∀ receiver : Fin count, receiver.val < index.val → ∀ time ∈ Icc 0 finish,
        |unstableShape motion time receiver| + |stableShape motion time receiver| ≤ radius) →
      (∀ source : Fin count, index.val < source.val →
        2 * (2 * Real.sqrt 2 * changed.omega (index.val + 1)) ≤ sourceRate * changed.omega (source.val + 1)) →
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
      ∀ suppliedLift : Fin 2 → ℝ → ℝ,
      (∀ side, ContinuousOn (suppliedLift side) (Icc 0 finish)) →
      (∀ side, suppliedLift side 0 = phase (index.val + 1)) →
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (suppliedLift side time : ℂ))) →
      let state := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift index time + raw time
      let allForeign := prepared.selectedForeignForcing (Finset.univ.erase index) index
      ContinuousOn state (Icc 0 finish) ∧ ContinuousOn allForeign (Icc 0 finish) ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * allForeign time) volume 0 finish ∧
      (∀ origin magnitude action : ℝ, 0 ≤ magnitude → 0 ≤ action →
        (∀ time ∈ Icc 0 finish, state time ≤ magnitude * Real.exp (growth * (time - origin))) →
        (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * allForeign time) ≤ action * Real.exp (-growth * origin) →
        actionCost ≤ 2 * omega * indexedReferenceSize * finish +
          3 * constant * (magnitude + action) * Real.exp (growth * (finish - origin))) ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * shape time) volume 0 finish ∧
      (∀ time ∈ Icc 0 finish, prepared.finiteCoordinateForeignForcing index time +
        prepared.physicalForeignSourceForcing index time ≤ allForeign time) ∧
      ∀ origin : ℝ,
        (∀ time ∈ Icc 0 finish, shape time ≤ shapeMagnitude * changed.seed (index.val + 1) *
          Real.exp (growth * (time - origin))) →
        let knownSourceBudget := 8 * prepared.mixedSelectedFinerSourcePrefixBudget index sharpIncoming sharpOutgoing extent sourceRate
          entry initialDistance magnitude growth finish +
          (32 * followerConstant * (216360000 * changed.hessian + 576 * changed.strain) /
            (omega * changed.location (index.val + 1) ^ 4)) *
            prepared.mixedFollowerSourcePrefixBudget index commonIncoming commonOutgoing extent sourceRate
              entry initialDistance magnitude growth finish
        knownSourceBudget ≤ sourceMagnitude * changed.seed (index.val + 1) * Real.exp (-growth * origin) →
        changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) ≤ endpointSize →
        (∀ time ∈ Icc 0 finish, state time ≤ profileConstant * (2 * shapeMagnitude + sourceMagnitude) *
          changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) ∧
        (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * allForeign time) ≤
          (shapeMagnitude + sourceMagnitude) * changed.seed (index.val + 1) * Real.exp (-growth * origin) ∧
        actionCost ≤ 2 * omega * indexedReferenceSize * finish +
          3 * constant * (profileConstant * (2 * shapeMagnitude + sourceMagnitude) + shapeMagnitude + sourceMagnitude) *
            changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) ∧
        actionCost < actionTolerance ∧
        omega * (∫ time in (0 : ℝ)..finish, coefficient time) < actionTolerance := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, costThreshold, costThresholdPositive, costEighth, compatible, costCap, costCapPositive, costs⟩ :=
    exists_uniform_actual_profile_accumulated_coefficient_cost
  obtain ⟨profileThreshold, profileThresholdPositive, _, profileCap, profileCapPositive, profilesFactory⟩ :=
    exists_uniform_actual_given_map_shape_profile_endpoint graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨fullThreshold, fullThresholdPositive, _, fullCap, fullCapPositive, commonIncoming, commonIncomingNonnegative,
    commonOutgoing, commonOutgoingNonnegative, sharpIncoming, sharpIncomingNonnegative, sharpOutgoing, sharpOutgoingNonnegative, fulls⟩ :=
    exists_uniform_actual_mixed_all_foreign_closed_weighted_forcing graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  let rawCap := min costCap (min profileCap fullCap)
  let thresholdMax := min costThreshold (min profileThreshold fullThreshold)
  have capPositive : 0 < rawCap := lt_min costCapPositive (lt_min profileCapPositive fullCapPositive)
  have capCost : rawCap ≤ costCap := min_le_left _ _
  have capProfile : rawCap ≤ profileCap := (min_le_right _ _).trans (min_le_left _ _)
  have capFull : rawCap ≤ fullCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, thresholdMax, lt_min costThresholdPositive (lt_min profileThresholdPositive fullThresholdPositive),
    (min_le_left _ _).trans costEighth, compatible, rawCap, capPositive, commonIncoming, commonIncomingNonnegative,
    commonOutgoing, commonOutgoingNonnegative, sharpIncoming, sharpIncomingNonnegative, sharpOutgoing, sharpOutgoingNonnegative, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, constant, constantOne, costRadius, costRadiusPositive, costQuarter, costFactory⟩ :=
    costs factorPositive factorSmall
  obtain ⟨profileRadius, profileRadiusPositive, _, profileConstant, profileOne, profileRoot, profileEight, profileFactory⟩ :=
    profilesFactory factor factorPositive factorSmall
  obtain ⟨fullRadius, fullRadiusPositive, _, followerConstant, followerOne, ratioMin, ratioMinimum, fullRoot, fullEight, fullFactory⟩ :=
    fulls factor factorPositive factorSmall
  let rootMin := max profileRoot fullRoot
  let radius := min costRadius (min profileRadius fullRadius)
  have rootEight : 8 ≤ rootMin := profileEight.trans (le_max_left _ _)
  refine ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, constant, constantOne,
    profileConstant, profileOne, followerConstant, followerOne, ratioMin, ratioMinimum, rootMin, rootEight,
    radius, lt_min costRadiusPositive (lt_min profileRadiusPositive fullRadiusPositive), (min_le_left _ _).trans costQuarter, ?_⟩
  intro shapeMagnitude sourceMagnitude actionTolerance shapeMagnitudeNonnegative sourceMagnitudeNonnegative actionPositive
  let coefficientSize := 3 * constant * (profileConstant * (2 * shapeMagnitude + sourceMagnitude) + shapeMagnitude + sourceMagnitude)
  have coefficientNonnegative : 0 ≤ coefficientSize := by dsimp only [coefficientSize]; positivity
  let endpointSize := actionTolerance / (4 * (1 + coefficientSize))
  have denominatorPositive : 0 < 4 * (1 + coefficientSize) := by positivity
  refine ⟨endpointSize, div_pos actionPositive denominatorPositive, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive extent extentOne referenceConstant referenceNonnegative referenceAmplitude
    threshold thresholdBound orbit sectionTime boundaryConstant tolerance boundaryOne tolerancePositive toleranceOne
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have ratioBound : 2 ≤ scales.ratio := ((le_max_left _ _).trans ratioMinimum).trans ratioLarge
  filter_upwards [costFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      (thresholdBound.trans (min_le_left _ _)) referenceNonnegative tolerancePositive toleranceOne,
    profileFactory scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans ((min_le_right _ _).trans (min_le_left _ _))) referenceNonnegative boundaryOne,
    fullFactory scales scaleRoot ((le_max_right _ _).trans rootLarge) amplitudeIdentity ratioLarge alphaPositive extent extentOne
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans ((min_le_right _ _).trans (min_le_right _ _)))
      orbit sectionTime boundaryConstant 1 boundaryOne (by norm_num),
    scales.eventually_uniform_reference_index_rate_small ratioBound alphaPositive
      (mul_nonneg (zero_le_one.trans chartOne) referenceNonnegative) (show 0 < actionTolerance / 4 by positivity),
    eventually_ge_atTop (1 : ℝ)]
    with frequency costEstimate profileEstimate fullEstimate referenceSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal terminal terminalNonnegative terminalBound entry initialDistance direction
  dsimp only
  intro entries extents sourceRate sourceRatePositive magnitude sourceProfiles finish finishInside radialSmall targetSmall followerSmall sourceRates
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have sizeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateSize = prepared.finiteCoordinateSize := by
    funext graph coordinate lift source time
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.finiteCoordinateSize]
  have selectedInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).selectedForeignForcing = prepared.selectedForeignForcing := rfl
  have sharpInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).mixedSelectedFinerSourcePrefixBudget = prepared.mixedSelectedFinerSourcePrefixBudget := rfl
  have commonInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).mixedFollowerSourcePrefixBudget = prepared.mixedFollowerSourcePrefixBudget := rfl
  have costData := costEstimate count phase dipoleAngle (prepared.enlargeCap capCost) path index nonterminal finish finishInside.1
    (finishInside.2.trans terminalBound) radialSmall (fun time inside => (targetSmall time inside).trans (min_le_left _ _))
  simp only [rawInvariant, sizeInvariant, selectedInvariant] at costData
  dsimp only [CascadeSourcePreparedPair.enlargeCap] at costData
  refine ⟨costData.1, ?_⟩
  intro suppliedLift suppliedContinuous suppliedInitial suppliedPolar
  have costAt := costData.2 suppliedLift suppliedContinuous suppliedInitial suppliedPolar
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (index.val + 1)
  let growth := 2 * Real.sqrt 2 * omega
  let seed := changed.seed (index.val + 1)
  let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  let shape := fun time =>
    |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).1 -
      (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
    |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).2 -
      (referenceStraightenedShape prepared.reference graph coordinate index time).2|
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let state := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift index time + raw time
  let allForeign := prepared.selectedForeignForcing (Finset.univ.erase index) index
  let forcing := fun time => prepared.finiteCoordinateForeignForcing index time + prepared.physicalForeignSourceForcing index time
  let knownSourceBudget := 8 * prepared.mixedSelectedFinerSourcePrefixBudget index sharpIncoming sharpOutgoing extent sourceRate
    entry initialDistance magnitude growth finish +
    (32 * followerConstant * (216360000 * changed.hessian + 576 * changed.strain) / (omega * changed.location (index.val + 1) ^ 4)) *
      prepared.mixedFollowerSourcePrefixBudget index commonIncoming commonOutgoing extent sourceRate entry initialDistance magnitude growth finish
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaGrowth : omega ≤ growth := by
    have rootTwo : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    dsimp only [growth]; nlinarith only [omegaPositive, mul_nonneg omegaPositive.le (sub_nonneg.mpr rootTwo)]
  have fullData := fullEstimate count phase dipoleAngle (prepared.enlargeCap capFull) path index nonterminal terminal terminalNonnegative terminalBound
    entry initialDistance direction entries extents sourceRate sourceRatePositive magnitude (by simpa only [rawInvariant] using sourceProfiles)
    finish finishInside radialSmall (fun time inside => (targetSmall time inside).trans ((min_le_right _ _).trans (min_le_right _ _)))
    (fun receiver below time inside => (followerSmall receiver below time inside).trans ((min_le_right _ _).trans (min_le_right _ _)))
    growth omegaGrowth sourceRates
  dsimp only at fullData
  simp only [selectedInvariant, sharpInvariant, commonInvariant] at fullData
  dsimp only [CascadeSourcePreparedPair.enlargeCap] at fullData
  rw [← prepared.referenceIdentity] at fullData
  obtain ⟨_, _, shapeI, allI, literalBound, allBound⟩ := fullData
  simp only [one_mul, add_assoc] at allBound
  change (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * allForeign time) ≤
    (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * shape time) + knownSourceBudget at allBound
  refine ⟨costAt.1, costAt.2.1, costAt.2.2.1, costAt.2.2.2, shapeI, literalBound, ?_⟩
  intro origin shapeProfile
  intro knownBound endpointBound
  change knownSourceBudget ≤ sourceMagnitude * seed * Real.exp (-growth * origin) at knownBound
  change seed * Real.exp (growth * (finish - origin)) ≤ endpointSize at endpointBound
  have finishOne : finish ≤ 1 := finishInside.2.trans (terminalBound.trans path.stopBound)
  have seedNonnegative : 0 ≤ seed := by dsimp only [seed, Scales.seed]; positivity
  have shapeActionBound : (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * shape time) ≤
      shapeMagnitude * seed * Real.exp (-growth * origin) := by
    have upperI := (continuous_const : Continuous (fun _ : ℝ => shapeMagnitude * seed * Real.exp (-growth * origin))).intervalIntegrable (μ := volume) 0 finish
    have comparison := intervalIntegral.integral_mono_on finishInside.1 shapeI upperI (by
      intro time inside
      have scaled := mul_le_mul_of_nonneg_left (shapeProfile time inside) (Real.exp_pos (-growth * time)).le
      have cancellation : Real.exp (-growth * time) * Real.exp (growth * (time - origin)) = Real.exp (-growth * origin) := by
        rw [← Real.exp_add]; congr 1; ring
      convert scaled using 1; rw [mul_left_comm, cancellation])
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at comparison
    exact comparison.trans (mul_le_of_le_one_left (by positivity) finishOne)
  have selectedActionBound : (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * allForeign time) ≤
      ((shapeMagnitude + sourceMagnitude) * seed) * Real.exp (-growth * origin) := by
    nlinarith only [allBound, shapeActionBound, knownBound]
  have profileData := profileEstimate count phase dipoleAngle (prepared.enlargeCap capProfile) path index nonterminal finish finishInside.1
    (finishInside.2.trans terminalBound) (fun time inside => (targetSmall time inside).trans ((min_le_right _ _).trans (min_le_left _ _)))
    suppliedLift suppliedContinuous suppliedInitial suppliedPolar
  simp only [rawInvariant, sizeInvariant] at profileData
  dsimp only [CascadeSourcePreparedPair.enlargeCap] at profileData
  obtain ⟨_, _, _, _, forcingI, profileBound⟩ := profileData
  have forcingActionBound : (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * forcing time) ≤
      ((shapeMagnitude + sourceMagnitude) * seed) * Real.exp (-growth * origin) := by
    apply le_trans _ selectedActionBound
    exact intervalIntegral.integral_mono_on finishInside.1 forcingI allI
      (fun time inside => mul_le_mul_of_nonneg_left (literalBound time inside) (Real.exp_pos _).le)
  have stateProfile : ∀ time ∈ Icc 0 finish, state time ≤ profileConstant * (2 * shapeMagnitude + sourceMagnitude) * seed *
      Real.exp (growth * (time - origin)) := by
    intro time inside
    have actual := profileBound origin (shapeMagnitude * seed) ((shapeMagnitude + sourceMagnitude) * seed) (by positivity) (by positivity)
      shapeProfile forcingActionBound time inside
    exact actual.trans_eq (by ring)
  have costBound := costAt.2.2.2 origin (profileConstant * (2 * shapeMagnitude + sourceMagnitude) * seed)
    ((shapeMagnitude + sourceMagnitude) * seed) (by positivity) (by positivity) stateProfile selectedActionBound
  have displayedBound := costBound.trans_eq (show _ = 2 * omega * referenceSize * finish +
      coefficientSize * (seed * Real.exp (growth * (finish - origin))) by dsimp only [coefficientSize]; ring)
  have actualReference := referenceSmall (index.val + 1)
  change 0 ≤ omega * referenceSize ∧ omega * referenceSize < actionTolerance / 4 at actualReference
  have baselineSmall : 2 * omega * referenceSize * finish < actionTolerance / 2 := by
    have finiteBound := mul_le_of_le_one_right actualReference.1 finishOne
    nlinarith only [finiteBound, actualReference.2]
  have exposureNonnegative : 0 ≤ seed * Real.exp (growth * (finish - origin)) := by positivity
  have endpointIdentity : 4 * (1 + coefficientSize) * endpointSize = actionTolerance := by
    dsimp only [endpointSize]; field_simp
  have exposureSmall : coefficientSize * (seed * Real.exp (growth * (finish - origin))) ≤ actionTolerance / 4 := by
    have scaled := mul_le_mul_of_nonneg_left endpointBound denominatorPositive.le
    rw [endpointIdentity] at scaled
    nlinarith only [scaled, exposureNonnegative]
  have strictCost := displayedBound.trans_lt (show _ < actionTolerance by linarith only [baselineSmall, exposureSmall, actionPositive])
  obtain ⟨_, _, _, _, _, _, coefficientBound, _⟩ := costData.1.1.1
  refine ⟨stateProfile, selectedActionBound, ?_, strictCost, coefficientBound.trans_lt strictCost⟩
  convert displayedBound using 1
  dsimp only [coefficientSize]
  ring

end EulerNonuniqueness.Paper

