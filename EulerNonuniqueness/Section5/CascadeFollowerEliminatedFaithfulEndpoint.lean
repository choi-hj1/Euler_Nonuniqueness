import EulerNonuniqueness.Section5.CascadeFaithfulShapeWeightedEndpoint
import EulerNonuniqueness.Section5.CascadeFollowerEliminatedWeightedForcing

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_follower_eliminated_faithful_endpoint :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ stableConstant ≥ (1 : ℝ), ∃ actionDilationConstant ≥ (0 : ℝ), ∃ finiteConstant ≥ (1 : ℝ),
      ∃ memoryConstant ≥ (1 : ℝ), ∃ radiusCoefficient ≥ (1 : ℝ),
      ∃ shapeConstant ≥ (1 : ℝ), ∃ forcingConstant ≥ (1 : ℝ), ∃ endpointConstant ≥ (1 : ℝ),
      ∃ macroConstant ≥ (1 : ℝ), ∃ followerConstant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
      max 2 (4 * followerConstant) ≤ scales.ratio → 0 < scales.alpha →
      ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
      ∀ {boundaryConstant threshold referenceConstant tolerance returnTolerance : ℝ}, 1 ≤ boundaryConstant → threshold ≤ thresholdMax → 0 ≤ referenceConstant → 0 < tolerance → 0 < returnTolerance →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
      (∀ receiver : Fin count, receiver.val < index.val → ∀ time ∈ Icc 0 finish,
        |unstableShape prepared.trajectory.movingFamily.patchMotion time receiver| +
          |stableShape prepared.trajectory.movingFamily.patchMotion time receiver| ≤ radius) →
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
        (tolerance + actionDilationConstant * changed.strain + actionDilationConstant * omega * epsilon) * center time +
        actionDilationConstant * omega * epsilon * raw time + actionDilationConstant * difference time +
        actionDilationConstant * epsilon * ∑ patch : Fin 4, foreign patch time
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
      (ContinuousOn coefficient (Icc 0 finish) ∧ ContinuousOn dilationMajorant (Icc 0 finish) ∧
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
      ∃ lift : Fin 2 → ℝ → ℝ,
        let size := prepared.finiteCoordinateSize graph coordinate lift index
        let finiteForcing := prepared.finiteCoordinateForeignForcing index
        let physical := prepared.physicalForeignSourceForcing index
        let allForcing := prepared.selectedForeignForcing (Finset.univ.erase index) index
        let finerForcing := prepared.selectedForeignForcing
          (Finset.univ.filter (fun source : Fin count => index.val < source.val ∧ source ≠ index)) index
        let remaining := prepared.followerStrictlyFinerForcing index
        let rho := 216360000 * changed.hessian + 576 * changed.strain
        let boundaryRadius := radiusCoefficient / (scaleRoot ^ 2 * omega ^ 2)
        let distance := fun time => ∑ patch : Fin 4,
          prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonBoundaryDistance
            (finProdFinEquiv (index, patch)) (patchSign patch * changed.amplitude * omega ^ 4) time boundaryRadius
            (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time)
            (prepared.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time)
        let drive := fun time => omega * center time + physical time
        let memoryRate := memoryConstant * (1 + omega * epsilon)
        let memory := fun time => memoryConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (memoryRate * (time - current)) * drive current
        (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
        (∀ side, ∀ time ∈ Icc 0 finish,
          positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
            (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
              Complex.exp (Complex.I * (lift side time : ℂ))) ∧
        ContinuousOn (prepared.finiteCoordinateSize graph coordinate lift index) (Icc 0 finish) ∧
        prepared.finiteCoordinateSize graph coordinate lift index 0 = 0 ∧
        ContinuousOn (prepared.finiteCoordinateForeignForcing index) (Icc 0 finish) ∧
        IntervalIntegrable (prepared.finiteCoordinateForeignForcing index) volume 0 finish ∧
        (∀ time ∈ Icc 0 finish,
          prepared.finiteCoordinateSize graph coordinate lift index time ≤ finiteConstant *
            ∫ current in (0 : ℝ)..time,
              ({scales with frequency := frequency} : Scales).omega (index.val + 1) *
                (prepared.finiteCoordinateSize graph coordinate lift index current +
                  (({scales with frequency := frequency} : Scales).radius (index.val + 1) ^ 2 /
                    ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2) *
                    ∑ patch : Fin 4, prepared.rawSourceShapeBudget current index patch) +
                prepared.finiteCoordinateForeignForcing index current) ∧
        (ContinuousOn memory (Icc 0 path.stop) ∧ IntervalIntegrable memory volume 0 path.stop ∧
          memory 0 = 0 ∧ distance 0 = 0 ∧
          (∀ time ∈ Icc 0 path.stop, 0 ≤ memory time ∧ distance time ≤ memory time ∧
            (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) ≤ memoryConstant * memory time) ∧
          ∀ start ∈ Icc 0 path.stop, ∀ time ∈ Icc start path.stop,
            memory time = Real.exp (memoryRate * (time - start)) * memory start +
              memoryConstant * ∫ current in start..time,
                Real.exp (memoryRate * (time - current)) * drive current) ∧
        memoryRate ≤ 2 * memoryConstant ∧ memoryRate ≤ omega / 2 ∧
        ContinuousOn physical (Icc 0 finish) ∧
        (∀ time ∈ Icc 0 path.stop, ∀ weight : ℝ, omega ≤ weight →
          IntervalIntegrable (fun current => Real.exp (-weight * current) * memory current) volume 0 time ∧
          IntervalIntegrable (fun current => Real.exp (-weight * current) * center current) volume 0 time ∧
          IntervalIntegrable (fun current => Real.exp (-weight * current) * physical current) volume 0 time ∧
          (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * memory current) ≤
            (2 * memoryConstant / weight) *
              (omega * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * center current) +
                ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * physical current)) ∧
        ContinuousOn finerForcing (Icc 0 finish) ∧ ContinuousOn remaining (Icc 0 finish) ∧
        ∀ weight : ℝ, omega ≤ weight → ∀ time ∈ Icc 0 finish,
          IntervalIntegrable (fun current => Real.exp (-weight * current) * size current) volume 0 time ∧
          IntervalIntegrable (fun current => Real.exp (-weight * current) * shape current) volume 0 time ∧
          IntervalIntegrable (fun current => Real.exp (-weight * current) * (finiteForcing current + physical current)) volume 0 time ∧
          IntervalIntegrable (fun current => Real.exp (-weight * current) * (size current + memory current)) volume 0 time ∧
          (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (size current + memory current)) ≤
            shapeConstant * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * shape current) +
            (forcingConstant / weight) * ∫ current in (0 : ℝ)..time,
              Real.exp (-weight * current) * (finiteForcing current + physical current) ∧
          size time + memory time ≤ endpointConstant * Real.exp (weight * time) *
            (omega * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * shape current) +
              ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (finiteForcing current + physical current)) ∧
          IntervalIntegrable (fun current => Real.exp (-weight * current) * allForcing current) volume 0 time ∧
          IntervalIntegrable (fun current => Real.exp (-weight * current) * finerForcing current) volume 0 time ∧
          IntervalIntegrable (fun current => Real.exp (-weight * current) * remaining current) volume 0 time ∧
          size time + memory time ≤ endpointConstant * Real.exp (weight * time) *
            ((omega + 2 * macroConstant * returnTolerance) *
                (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * shape current) +
              2 * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * finerForcing current) +
              (4 * followerConstant * rho / (omega * changed.location (index.val + 1) ^ 4)) *
                ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * remaining current) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, endpointThreshold, endpointThresholdPositive, endpointThresholdEighth, compatible,
    endpointCap, endpointCapPositive, endpointFactory⟩ := exists_uniform_actual_faithful_shape_weighted_endpoint
  obtain ⟨eliminationThreshold, eliminationThresholdPositive, _, eliminationCap, eliminationCapPositive, eliminationFactory⟩ :=
    exists_uniform_actual_follower_eliminated_weighted_forcing graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  let thresholdMax := min endpointThreshold eliminationThreshold
  let rawCap := min endpointCap eliminationCap
  have endpointCapBound : rawCap ≤ endpointCap := min_le_left _ _
  have eliminationCapBound : rawCap ≤ eliminationCap := min_le_right _ _
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, thresholdMax, lt_min endpointThresholdPositive eliminationThresholdPositive,
    (min_le_left _ _).trans endpointThresholdEighth, compatible, rawCap, lt_min endpointCapPositive eliminationCapPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, finiteConstant, finiteOne, memoryConstant, memoryOne,
    radiusCoefficient, radiusCoefficientOne, shapeConstant, shapeOne, forcingConstant, forcingOne, endpointConstant, endpointOne,
    endpointRoot, endpointRootEight, endpointRadius, endpointRadiusPositive, endpointRadiusQuarter, endpoints⟩ :=
    endpointFactory factorPositive factorSmall
  obtain ⟨eliminationRadius, eliminationRadiusPositive, _, macroConstant, macroOne, followerConstant, followerOne,
    eliminationRoot, _, eliminations⟩ := eliminationFactory factor factorPositive factorSmall
  let radius := min endpointRadius eliminationRadius
  let rootMin := max endpointRoot eliminationRoot
  refine ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, finiteConstant, finiteOne, memoryConstant, memoryOne,
    radiusCoefficient, radiusCoefficientOne, shapeConstant, shapeOne, forcingConstant, forcingOne, endpointConstant, endpointOne,
    macroConstant, macroOne, followerConstant, followerOne, rootMin, endpointRootEight.trans (le_max_left _ _),
    radius, lt_min endpointRadiusPositive eliminationRadiusPositive, (min_le_left _ _).trans endpointRadiusQuarter, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive orbit sectionTime boundaryConstant threshold
    referenceConstant tolerance returnTolerance boundaryOne thresholdBound referenceNonnegative tolerancePositive returnTolerancePositive
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  filter_upwards [endpoints scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive
      orbit sectionTime boundaryOne (thresholdBound.trans (min_le_left _ _)) referenceNonnegative tolerancePositive,
    eliminations scales scaleRoot ((le_max_right _ _).trans rootLarge) amplitudeIdentity ratioLarge alphaPositive
      threshold referenceConstant boundaryConstant (thresholdBound.trans (min_le_right _ _)) referenceNonnegative boundaryOne
      orbit sectionTime returnTolerance returnTolerancePositive]
    with frequency endpointEstimate eliminationEstimate
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound
    radialSmall targetSmall followerSmall
  have centeredInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have sizeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateSize = prepared.finiteCoordinateSize := rfl
  have finiteInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateForeignForcing = prepared.finiteCoordinateForeignForcing := rfl
  have physicalInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).physicalForeignSourceForcing = prepared.physicalForeignSourceForcing := rfl
  have selectedInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).selectedForeignForcing = prepared.selectedForeignForcing := rfl
  have remainingInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).followerStrictlyFinerForcing = prepared.followerStrictlyFinerForcing := rfl
  have endpointData := endpointEstimate count phase dipoleAngle (prepared.enlargeCap endpointCapBound) path index nonterminal
    finish finishNonnegative finishBound radialSmall (fun time inside => (targetSmall time inside).trans (min_le_left _ _))
  simp only [centeredInvariant, rawInvariant, sizeInvariant, finiteInvariant, physicalInvariant] at endpointData
  dsimp only [CascadeSourcePreparedPair.enlargeCap] at endpointData
  obtain ⟨coefficientData, lift, liftProperties, polar, sizeContinuous, sizeInitial, forcingContinuous, forcingIntegrable,
    coordinateHistory, memoryData, rateBound, rateHalf, physicalContinuous, memoryWeighted, parentEndpoints⟩ := endpointData
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let relative := fun time => referenceStraightenedShape first graph coordinate index time -
    referenceStraightenedShape second graph coordinate index time
  let shape := fun time => |(relative time).1| + |(relative time).2|
  let size := prepared.finiteCoordinateSize graph coordinate lift index
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let physical := prepared.physicalForeignSourceForcing index
  let finiteForcing := prepared.finiteCoordinateForeignForcing index
  let allForcing := prepared.selectedForeignForcing (Finset.univ.erase index) index
  let finerForcing := prepared.selectedForeignForcing
    (Finset.univ.filter (fun source : Fin count => index.val < source.val ∧ source ≠ index)) index
  let remaining := prepared.followerStrictlyFinerForcing index
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let memoryRate := memoryConstant * (1 + omega * epsilon)
  let memory := fun time => memoryConstant * ∫ current in (0 : ℝ)..time,
    Real.exp (memoryRate * (time - current)) * (omega * prepared.rawSourceCenteredState current index + physical current)
  let eliminationAt := fun (weight : ℝ) (omegaWeight : omega ≤ weight) (time : ℝ) (inside : time ∈ Icc 0 finish) =>
    eliminationEstimate count phase dipoleAngle (prepared.enlargeCap eliminationCapBound) path index nonterminal time inside.1
      (inside.2.trans finishBound) (fun current member => radialSmall current ⟨member.1, member.2.trans inside.2⟩)
      (fun current member => (targetSmall current ⟨member.1, member.2.trans inside.2⟩).trans (min_le_right _ _))
      (fun receiver below current member =>
        (followerSmall receiver below current ⟨member.1, member.2.trans inside.2⟩).trans (min_le_right _ _)) weight omegaWeight
  have full := eliminationAt omega le_rfl finish ⟨finishNonnegative, le_rfl⟩
  dsimp only [eliminationAt] at full
  simp only [selectedInvariant, remainingInvariant, finiteInvariant, physicalInvariant] at full
  refine ⟨coefficientData, lift, liftProperties, polar, sizeContinuous, sizeInitial, forcingContinuous, forcingIntegrable,
    coordinateHistory, memoryData, rateBound, rateHalf, physicalContinuous, memoryWeighted, full.2.2.1, full.2.2.2.1, ?_⟩
  intro weight omegaWeight time inside
  have original := parentEndpoints weight omegaWeight time inside
  have eliminated := eliminationAt weight omegaWeight time inside
  dsimp only [eliminationAt] at eliminated
  simp only [selectedInvariant, remainingInvariant, finiteInvariant, physicalInvariant] at eliminated
  obtain ⟨_, _, _, _, _, _, allIntegrable, _, finerIntegrable, remainingIntegrable, pointwise, eliminatedBound⟩ := eliminated
  have actualBound :
      (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * allForcing current) ≤
        2 * macroConstant * returnTolerance * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * shape current) +
        2 * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * finerForcing current) +
        (4 * followerConstant * rho / (omega * changed.location (index.val + 1) ^ 4)) *
          ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * remaining current := by
    simpa only [shape, relative, first, second, Prod.fst_sub, Prod.snd_sub, prepared.referenceIdentity] using eliminatedBound
  have forceComparison :
      (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (finiteForcing current + physical current)) ≤
        ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * allForcing current :=
    intervalIntegral.integral_mono_on inside.1 original.2.2.1 allIntegrable
      (fun current member => mul_le_mul_of_nonneg_left (pointwise current member) (Real.exp_pos _).le)
  refine ⟨original.1, original.2.1, original.2.2.1, original.2.2.2.1, original.2.2.2.2.1,
    original.2.2.2.2.2, allIntegrable, finerIntegrable, remainingIntegrable, ?_⟩
  have combined :
      omega * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * shape current) +
          (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (finiteForcing current + physical current)) ≤
        (omega + 2 * macroConstant * returnTolerance) *
          (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * shape current) +
        2 * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * finerForcing current) +
        (4 * followerConstant * rho / (omega * changed.location (index.val + 1) ^ 4)) *
          ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * remaining current := by
    nlinarith only [forceComparison, actualBound]
  have endpointBound : size time + memory time ≤ endpointConstant * Real.exp (weight * time) *
      (omega * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * shape current) +
        ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (finiteForcing current + physical current)) :=
    original.2.2.2.2.2
  exact endpointBound.trans (mul_le_mul_of_nonneg_left combined
    (mul_nonneg (zero_le_one.trans endpointOne) (Real.exp_pos _).le))

end EulerNonuniqueness.Paper

