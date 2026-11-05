import EulerNonuniqueness.General.WeightedCoupledEndpoint
import EulerNonuniqueness.Section5.CascadeIntegratedCoefficientFiniteCoordinateHistory
import EulerNonuniqueness.Section5.CascadeFaithfulBoundaryMemoryWeightedReturn
import EulerNonuniqueness.Section5.CascadeFiniteCoordinateShapeArbitraryWeightReturn

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem faithful_joint_weighted_scalar
    {coordinate memory center shape forcing physical coordinateConstant memoryConstant geometryConstant omega weight : ℝ}
    (coordinateNonnegative : 0 ≤ coordinate) (forcingNonnegative : 0 ≤ forcing)
    (_coordinateConstantNonnegative : 0 ≤ coordinateConstant) (memoryConstantNonnegative : 0 ≤ memoryConstant)
    (geometryConstantNonnegative : 0 ≤ geometryConstant) (omegaNonnegative : 0 ≤ omega)
    (weightPositive : 0 < weight) (omegaWeight : omega ≤ weight)
    (coordinateBound : coordinate ≤ coordinateConstant * shape +
      (coordinateConstant / weight) * (forcing + physical))
    (memoryBound : memory ≤ (2 * memoryConstant / weight) * (omega * center + physical))
    (centerBound : center ≤ geometryConstant * coordinate) :
    coordinate + memory ≤ ((1 + 2 * memoryConstant * geometryConstant) * coordinateConstant) * shape +
      (((1 + 2 * memoryConstant * geometryConstant) * coordinateConstant + 2 * memoryConstant) / weight) *
        (forcing + physical) := by
  have centerScaled := mul_le_mul_of_nonneg_left centerBound
    (show 0 ≤ 2 * memoryConstant / weight * omega by positivity)
  have ratio : omega / weight ≤ 1 := (div_le_one weightPositive).mpr omegaWeight
  have ratioScaled := mul_le_mul_of_nonneg_right ratio
    (show 0 ≤ 2 * memoryConstant * geometryConstant * coordinate by positivity)
  have memoryUpper : memory ≤ 2 * memoryConstant * geometryConstant * coordinate +
      (2 * memoryConstant / weight) * physical := by
    calc
      memory ≤ (2 * memoryConstant / weight) * (omega * center + physical) := memoryBound
      _ = (2 * memoryConstant / weight * omega) * center + (2 * memoryConstant / weight) * physical := by ring
      _ ≤ (2 * memoryConstant / weight * omega) * (geometryConstant * coordinate) + (2 * memoryConstant / weight) * physical :=
        add_le_add_right centerScaled _
      _ = (omega / weight) * (2 * memoryConstant * geometryConstant * coordinate) + (2 * memoryConstant / weight) * physical := by ring
      _ ≤ 2 * memoryConstant * geometryConstant * coordinate + (2 * memoryConstant / weight) * physical := by
        simpa only [one_mul] using add_le_add_right ratioScaled ((2 * memoryConstant / weight) * physical)
  have coordinateScaled := mul_le_mul_of_nonneg_left coordinateBound
    (show 0 ≤ 1 + 2 * memoryConstant * geometryConstant by positivity)
  have forcingScaled := mul_nonneg
    (show 0 ≤ 2 * memoryConstant / weight by positivity) forcingNonnegative
  calc
    coordinate + memory ≤ coordinate + (2 * memoryConstant * geometryConstant * coordinate + (2 * memoryConstant / weight) * physical) :=
      add_le_add_left memoryUpper _
    _ = (1 + 2 * memoryConstant * geometryConstant) * coordinate + (2 * memoryConstant / weight) * physical := by ring
    _ ≤ (1 + 2 * memoryConstant * geometryConstant) *
        (coordinateConstant * shape + (coordinateConstant / weight) * (forcing + physical)) + (2 * memoryConstant / weight) * physical :=
      add_le_add_right coordinateScaled _
    _ ≤ (1 + 2 * memoryConstant * geometryConstant) *
        (coordinateConstant * shape + (coordinateConstant / weight) * (forcing + physical)) + (2 * memoryConstant / weight) * physical +
          (2 * memoryConstant / weight) * forcing := le_add_of_nonneg_right forcingScaled
    _ = _ := by ring

theorem exists_uniform_actual_faithful_shape_weighted_endpoint :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ stableConstant ≥ (1 : ℝ), ∃ actionDilationConstant ≥ (0 : ℝ), ∃ finiteConstant ≥ (1 : ℝ),
      ∃ memoryConstant ≥ (1 : ℝ), ∃ radiusCoefficient ≥ (1 : ℝ),
      ∃ shapeConstant ≥ (1 : ℝ), ∃ forcingConstant ≥ (1 : ℝ), ∃ endpointConstant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
      2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
      ∀ {boundaryConstant threshold referenceConstant tolerance : ℝ}, 1 ≤ boundaryConstant → threshold ≤ thresholdMax → 0 ≤ referenceConstant → 0 < tolerance →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
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
              ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (finiteForcing current + physical current)) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, bridgeThreshold, bridgeThresholdPositive, bridgeThresholdEighth, compatible,
    bridgeCap, bridgeCapPositive, bridgeFactory⟩ :=
    exists_uniform_actual_integrated_coefficient_finite_coordinate_history
  obtain ⟨weightedThreshold, weightedThresholdPositive, _, weightedCap, weightedCapPositive, weightedFactory⟩ :=
    exists_uniform_actual_finite_coordinate_shape_arbitrary_weight_return graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨geometryRadius, geometryPositive, _, geometryConstant, geometryOne, geometries⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨memoryCap, memoryPositive, memoryFactory⟩ := exists_uniform_actual_faithful_boundary_memory_weighted_return
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let cap := min bridgeCap (min weightedCap (min memoryCap continuityCap))
  have capPositive : 0 < cap := lt_min bridgeCapPositive (lt_min weightedCapPositive (lt_min memoryPositive continuityPositive))
  have bridgeCapBound : cap ≤ bridgeCap := min_le_left _ _
  have weightedCapBound : cap ≤ weightedCap := (min_le_right _ _).trans (min_le_left _ _)
  have memoryCapBound : cap ≤ memoryCap := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have continuityCapBound : cap ≤ continuityCap := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  let thresholdMax := min bridgeThreshold weightedThreshold
  have thresholdEighth : thresholdMax ≤ 1 / 8 := (min_le_left _ _).trans bridgeThresholdEighth
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, thresholdMax, lt_min bridgeThresholdPositive weightedThresholdPositive,
    thresholdEighth, compatible, cap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨stableConstant, stableOne, actionDilationConstant, actionDilationNonnegative, coordinateConstant, coordinateOne,
    coordinateRadius, coordinatePositive, coordinateQuarter, coordinates⟩ := bridgeFactory factorPositive factorSmall
  obtain ⟨weightedRadius, weightedPositive, _, weightedConstant, weightedOne, weightedRoot, weightedEight, weights⟩ :=
    weightedFactory factor factorPositive factorSmall
  obtain ⟨memoryConstant, memoryOne, radiusCoefficient, radiusCoefficientOne, memoryRoot, memoryEight, memories⟩ :=
    memoryFactory factor factorPositive factorOne
  let radius := min coordinateRadius (min weightedRadius geometryRadius)
  let rootMin := max weightedRoot memoryRoot
  have rootEight : 8 ≤ rootMin := weightedEight.trans (le_max_left _ _)
  have memoryNonnegativeConstant : 0 ≤ memoryConstant := zero_le_one.trans memoryOne
  have geometryNonnegativeConstant : 0 ≤ geometryConstant := zero_le_one.trans geometryOne
  have coordinateNonnegativeConstant : 0 ≤ coordinateConstant := zero_le_one.trans coordinateOne
  have weightedNonnegativeConstant : 0 ≤ weightedConstant := zero_le_one.trans weightedOne
  let combinedConstant := max (coordinateConstant * memoryConstant) (memoryConstant * geometryConstant)
  have combinedOne : 1 ≤ combinedConstant :=
    coordinateOne.trans ((le_mul_of_one_le_right coordinateNonnegativeConstant memoryOne).trans (le_max_left _ _))
  have combinedNonnegative : 0 ≤ combinedConstant := zero_le_one.trans combinedOne
  let shapeConstant := (1 + 2 * memoryConstant * geometryConstant) * weightedConstant
  let forcingConstant := shapeConstant + 2 * memoryConstant
  have shapeOne : 1 ≤ shapeConstant := by
    have factorOne' : 1 ≤ 1 + 2 * memoryConstant * geometryConstant := by
      have nonnegative : 0 ≤ 2 * memoryConstant * geometryConstant := by positivity
      linarith only [nonnegative]
    exact one_le_mul_of_one_le_of_one_le factorOne' weightedOne
  have forcingOne : 1 ≤ forcingConstant := by dsimp only [forcingConstant]; linarith only [shapeOne, memoryOne]
  have forcingConstantNonnegative : 0 ≤ forcingConstant := zero_le_one.trans forcingOne
  let endpointConstant := max 1 (max (2 * combinedConstant * shapeConstant) (combinedConstant * (1 + 2 * forcingConstant)))
  refine ⟨stableConstant, stableOne, actionDilationConstant, actionDilationNonnegative, coordinateConstant, coordinateOne,
    memoryConstant, memoryOne, radiusCoefficient, radiusCoefficientOne, shapeConstant, shapeOne,
    forcingConstant, forcingOne, endpointConstant, le_max_left _ _, rootMin, rootEight,
    radius, lt_min coordinatePositive (lt_min weightedPositive geometryPositive), (min_le_left _ _).trans coordinateQuarter, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive orbit sectionTime boundaryConstant threshold referenceConstant tolerance
    boundaryOne thresholdBound referenceNonnegative tolerancePositive
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  filter_upwards [coordinates scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      (thresholdBound.trans (min_le_left _ _)) referenceNonnegative tolerancePositive,
    weights scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans (min_le_right _ _)) referenceNonnegative boundaryOne,
    memories scales scaleRoot ((le_max_right _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
      thresholdSmall referenceNonnegative boundaryOne orbit sectionTime,
    geometries scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) factorPositive (factorSmall.trans (by norm_num)) thresholdSmall referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    scales.eventually_cascade_physical_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_ge_atTop (1 : ℝ)]
    with frequency coordinateEstimate weightedEstimate memoryEstimate geometryEstimate coherence physicalEstimate frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall small
  have centeredInvariant {largerCap : ℝ} (larger : cap ≤ largerCap) :
      (prepared.enlargeCap larger).rawSourceCenteredState = prepared.rawSourceCenteredState := by rfl
  have rawInvariant {largerCap : ℝ} (larger : cap ≤ largerCap) :
      (prepared.enlargeCap larger).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have sizeInvariant {largerCap : ℝ} (larger : cap ≤ largerCap) :
      (prepared.enlargeCap larger).finiteCoordinateSize = prepared.finiteCoordinateSize := by rfl
  have forcingInvariant {largerCap : ℝ} (larger : cap ≤ largerCap) :
      (prepared.enlargeCap larger).finiteCoordinateForeignForcing = prepared.finiteCoordinateForeignForcing := by rfl
  let coordinatePrepared := prepared.enlargeCap bridgeCapBound
  have bridge := coordinateEstimate count phase dipoleAngle coordinatePrepared path index nonterminal finish finishNonnegative finishBound radialSmall
    (fun time inside => (small time inside).trans (min_le_left _ _))
  dsimp only [coordinatePrepared] at bridge
  simp only [centeredInvariant, rawInvariant, sizeInvariant, forcingInvariant] at bridge
  dsimp only [CascadeSourcePreparedPair.enlargeCap] at bridge
  obtain ⟨coefficientData, lift, liftProperties, polar, sizeContinuous, sizeInitial, forcingContinuous, forcingIntegrable, coordinateHistory⟩ := bridge
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let relative := fun time => referenceStraightenedShape first graph coordinate index time -
    referenceStraightenedShape second graph coordinate index time
  let shape := fun time => |(relative time).1| + |(relative time).2|
  let size := prepared.finiteCoordinateSize graph coordinate lift index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let center := fun time => prepared.rawSourceCenteredState time index
  let forcing := prepared.finiteCoordinateForeignForcing index
  let physical := prepared.physicalForeignSourceForcing index
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let rate := memoryConstant * (1 + omega * epsilon)
  let drive := fun time => omega * center time + physical time
  let memory := fun time => memoryConstant * ∫ current in (0 : ℝ)..time,
    Real.exp (rate * (time - current)) * drive current
  change ContinuousOn size (Icc 0 finish) at sizeContinuous
  change size 0 = 0 at sizeInitial
  change ContinuousOn forcing (Icc 0 finish) at forcingContinuous
  have relativeContinuous : ContinuousOn relative (Icc 0 finish) := coefficientData.2.2.2.2.2.2.2.2.1
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) :=
    ((continuous_fst.comp_continuousOn relativeContinuous).abs).add ((continuous_snd.comp_continuousOn relativeContinuous).abs)
  obtain ⟨geometryLift, geometryProperties, geometryPolar, _, _, geometryNonnegative, geometryBounds⟩ :=
    geometryEstimate prepared path index nonterminal finish finishNonnegative finishBound
      (fun time inside => (small time inside).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have sizeEquality := (coherence prepared path index finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans ((min_le_left _ _).trans coordinateQuarter))
    geometryLift lift (fun side => (geometryProperties side).1.continuousOn)
    (fun side => (liftProperties side).1.continuousOn)
    (fun side => (geometryProperties side).2.trans (liftProperties side).2.symm) geometryPolar polar).2.2 graph coordinate
  have sizeNonnegative (time : ℝ) (inside : time ∈ Icc 0 finish) : 0 ≤ size time :=
    (geometryNonnegative time).trans_eq (sizeEquality inside)
  have centerBound (time : ℝ) (inside : time ∈ Icc 0 finish) : center time ≤ geometryConstant * size time := by
    have actual := (geometryBounds time inside).1
    rw [sizeEquality inside] at actual
    exact actual
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have rawContinuous : ContinuousOn raw (Icc 0 finish) := continuousOn_finset_sum _
    (fun patch _ => ((stateContinuity prepared capPositive continuityCapBound path index).1 patch).mono subset)
  have centerContinuous : ContinuousOn center (Icc 0 finish) :=
    (stateContinuity prepared capPositive continuityCapBound path index).2.1.mono subset
  obtain ⟨_, physicalContinuousFull, physicalNonnegative, _⟩ := physicalEstimate count phase dipoleAngle prepared path index
  have physicalContinuous : ContinuousOn physical (Icc 0 finish) := physicalContinuousFull.mono subset
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive
    (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _)
  have omegaNonnegative : 0 ≤ omega := omegaPositive.le
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have forcingNonnegative (time : ℝ) : 0 ≤ forcing time := by
    have locationPositive := changed.location_pos (index.val + 1)
    dsimp only [forcing, CascadeSourcePreparedPair.finiteCoordinateForeignForcing]
    positivity
  have memoryData := memoryEstimate count phase dipoleAngle prepared capPositive memoryCapBound path index
  have memoryContinuousFull : ContinuousOn memory (Icc 0 path.stop) := memoryData.1.1
  have memoryContinuous : ContinuousOn memory (Icc 0 finish) := memoryContinuousFull.mono subset
  have memoryInitial : memory 0 = 0 := memoryData.1.2.2.1
  have memoryBounds := memoryData.1.2.2.2.2.1
  have rateOmega : rate ≤ omega / 2 := memoryData.2.2.1
  have epsilonOne : epsilon ≤ 1 := by
    have rateLower : omega * epsilon ≤ rate := by
      have scaled := le_mul_of_one_le_left (show 0 ≤ 1 + omega * epsilon by positivity) memoryOne
      dsimp only [rate]
      linarith only [scaled]
    exact (mul_le_mul_left omegaPositive).mp (rateLower.trans (rateOmega.trans (by linarith only [omegaPositive])))
  have memoryNonnegative (time : ℝ) (inside : time ∈ Icc 0 finish) : 0 ≤ memory time :=
    (memoryBounds time (subset inside)).1
  have rawMemory (time : ℝ) (inside : time ∈ Icc 0 finish) : raw time ≤ memoryConstant * memory time :=
    (memoryBounds time (subset inside)).2.2
  have coordinateBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      size time ≤ size 0 + combinedConstant * ∫ current in (0 : ℝ)..time,
        omega * (size current + epsilon * memory current) + forcing current := by
    have literalActual : size time ≤ coordinateConstant * ∫ current in (0 : ℝ)..time,
        omega * (size current + epsilon * raw current) + forcing current :=
      coordinateHistory time inside
    rw [sizeInitial, zero_add]
    have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have lowerContinuous : ContinuousOn (fun current => omega * (size current + epsilon * raw current) + forcing current) (Icc 0 time) :=
      (continuousOn_const.mul ((sizeContinuous.mono prefixSubset).add
        (continuousOn_const.mul (rawContinuous.mono prefixSubset)))).add (forcingContinuous.mono prefixSubset)
    have upperContinuous : ContinuousOn (fun current => memoryConstant *
        (omega * (size current + epsilon * memory current) + forcing current)) (Icc 0 time) :=
      continuousOn_const.mul ((continuousOn_const.mul ((sizeContinuous.mono prefixSubset).add
        (continuousOn_const.mul (memoryContinuous.mono prefixSubset)))).add (forcingContinuous.mono prefixSubset))
    have comparison := intervalIntegral.integral_mono_on inside.1
      (lowerContinuous.intervalIntegrable_of_Icc (μ := volume) inside.1)
      (upperContinuous.intervalIntegrable_of_Icc (μ := volume) inside.1) (by
        intro current member
        have rawScaled := mul_le_mul_of_nonneg_left (rawMemory current (prefixSubset member))
          (mul_nonneg omegaNonnegative epsilonNonnegative)
        have sizeScaled := le_mul_of_one_le_left
          (mul_nonneg omegaNonnegative (sizeNonnegative current (prefixSubset member))) memoryOne
        have forceScaled := le_mul_of_one_le_left (forcingNonnegative current) memoryOne
        nlinarith only [rawScaled, sizeScaled, forceScaled])
    rw [intervalIntegral.integral_const_mul] at comparison
    have integralNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time,
        omega * (size current + epsilon * memory current) + forcing current :=
      intervalIntegral.integral_nonneg inside.1 (fun current member => by
        exact add_nonneg (mul_nonneg omegaNonnegative
          (add_nonneg (sizeNonnegative current (prefixSubset member))
            (mul_nonneg epsilonNonnegative (memoryNonnegative current (prefixSubset member))))) (forcingNonnegative current))
    calc
      size time ≤ coordinateConstant * ∫ current in (0 : ℝ)..time,
          omega * (size current + epsilon * raw current) + forcing current := literalActual
      _ ≤ coordinateConstant * (memoryConstant * ∫ current in (0 : ℝ)..time,
          omega * (size current + epsilon * memory current) + forcing current) :=
        mul_le_mul_of_nonneg_left comparison coordinateNonnegativeConstant
      _ = (coordinateConstant * memoryConstant) * ∫ current in (0 : ℝ)..time,
          omega * (size current + epsilon * memory current) + forcing current := by ring
      _ ≤ combinedConstant * ∫ current in (0 : ℝ)..time,
          omega * (size current + epsilon * memory current) + forcing current :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) integralNonnegative
  have memoryBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      memory time ≤ memory 0 * Real.exp (rate * (time - 0)) +
        combinedConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * size current + physical current) := by
    rw [memoryInitial, zero_mul, zero_add]
    have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have kernelContinuous : Continuous (fun current : ℝ => Real.exp (rate * (time - current))) := by fun_prop
    have lowerIntegrable : IntervalIntegrable (fun current => Real.exp (rate * (time - current)) *
        (omega * center current + physical current)) volume 0 time := (kernelContinuous.continuousOn.mul
      ((continuousOn_const.mul (centerContinuous.mono prefixSubset)).add (physicalContinuous.mono prefixSubset))).intervalIntegrable_of_Icc (μ := volume) inside.1
    have upperIntegrable : IntervalIntegrable (fun current => geometryConstant * (Real.exp (rate * (time - current)) *
        (omega * size current + physical current))) volume 0 time := ((kernelContinuous.continuousOn.mul
      ((continuousOn_const.mul (sizeContinuous.mono prefixSubset)).add (physicalContinuous.mono prefixSubset))).intervalIntegrable_of_Icc
        (μ := volume) inside.1).const_mul geometryConstant
    have comparison := intervalIntegral.integral_mono_on inside.1 lowerIntegrable upperIntegrable (by
      intro current member
      have centered := mul_le_mul_of_nonneg_left (centerBound current (prefixSubset member)) omegaNonnegative
      have foreign := le_mul_of_one_le_left (physicalNonnegative current) geometryOne
      have scaled := mul_le_mul_of_nonneg_left (add_le_add centered foreign) (Real.exp_pos (rate * (time - current))).le
      exact scaled.trans_eq (by ring))
    rw [intervalIntegral.integral_const_mul] at comparison
    have integralNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time,
        Real.exp (rate * (time - current)) * (omega * size current + physical current) :=
      intervalIntegral.integral_nonneg inside.1 (fun current member => mul_nonneg (Real.exp_pos _).le
        (add_nonneg (mul_nonneg omegaNonnegative (sizeNonnegative current (prefixSubset member))) (physicalNonnegative current)))
    calc
      memory time = memoryConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * center current + physical current) := rfl
      _ ≤ memoryConstant * (geometryConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * size current + physical current)) :=
        mul_le_mul_of_nonneg_left comparison memoryNonnegativeConstant
      _ = (memoryConstant * geometryConstant) * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * size current + physical current) := by ring
      _ ≤ combinedConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * size current + physical current) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) integralNonnegative

  with_reducible_and_instances
    refine ⟨coefficientData, lift, liftProperties, polar, sizeContinuous, sizeInitial, forcingContinuous,
      forcingIntegrable, coordinateHistory, memoryData.1, memoryData.2.1, rateOmega, physicalContinuous, memoryData.2.2.2, ?_⟩
  intro weight omegaWeight time inside
  have weightPositive : 0 < weight := omegaPositive.trans_le omegaWeight
  have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have actualWeighted := weightedEstimate count phase dipoleAngle (prepared.enlargeCap weightedCapBound) path index nonterminal
    time inside.1 (inside.2.trans finishBound)
    (fun current member => (small current (prefixSubset member)).trans ((min_le_right _ _).trans (min_le_left _ _)))
    lift (fun side => (liftProperties side).1.continuousOn) (fun side => (liftProperties side).2)
    (fun side current member => polar side current (prefixSubset member)) weight omegaWeight
  dsimp only [CascadeSourcePreparedPair.enlargeCap] at actualWeighted
  rw [← prepared.referenceIdentity] at actualWeighted
  simp only [← Prod.fst_sub, ← Prod.snd_sub] at actualWeighted
  change IntervalIntegrable (fun current => Real.exp (-weight * current) * size current) volume 0 time ∧
    IntervalIntegrable (fun current => Real.exp (-weight * current) * shape current) volume 0 time ∧
    IntervalIntegrable (fun current => Real.exp (-weight * current) * (forcing current + physical current)) volume 0 time ∧
    (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * size current) ≤
      weightedConstant * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * shape current) +
      (weightedConstant / weight) * ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (forcing current + physical current)
    at actualWeighted
  have memoryWeighted := memoryData.2.2.2 time (subset inside) weight omegaWeight
  have weightContinuous : Continuous (fun current : ℝ => Real.exp (-weight * current)) := by fun_prop
  have forcingWeighted := (weightContinuous.continuousOn.mul (forcingContinuous.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have centerComparison := intervalIntegral.integral_mono_on inside.1 memoryWeighted.2.1
    (actualWeighted.1.const_mul geometryConstant) (by
      intro current member
      exact (mul_le_mul_of_nonneg_left (centerBound current (prefixSubset member)) (Real.exp_pos _).le).trans_eq (by ring))
  rw [intervalIntegral.integral_const_mul] at centerComparison
  have weightedSizeNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * size current :=
    intervalIntegral.integral_nonneg inside.1 (fun current member => mul_nonneg (Real.exp_pos _).le (sizeNonnegative current (prefixSubset member)))
  have weightedForcingNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * forcing current :=
    intervalIntegral.integral_nonneg inside.1 (fun current _ => mul_nonneg (Real.exp_pos _).le (forcingNonnegative current))
  have forceIdentity : (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (forcing current + physical current)) =
      (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * forcing current) +
      ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * physical current := by
    simp_rw [mul_add]
    exact intervalIntegral.integral_add forcingWeighted memoryWeighted.2.2.1
  have joint := faithful_joint_weighted_scalar weightedSizeNonnegative weightedForcingNonnegative
    weightedNonnegativeConstant memoryNonnegativeConstant geometryNonnegativeConstant omegaNonnegative weightPositive omegaWeight
    (actualWeighted.2.2.2.trans_eq (by rw [forceIdentity])) memoryWeighted.2.2.2 centerComparison
  have jointIntegrable := actualWeighted.1.add memoryWeighted.1
  have jointIdentity : (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (size current + memory current)) =
      (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * size current) +
      ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * memory current := by
    simp_rw [mul_add]
    exact intervalIntegral.integral_add actualWeighted.1 memoryWeighted.1
  have jointBound : (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (size current + memory current)) ≤
      shapeConstant * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * shape current) +
      (forcingConstant / weight) * ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (forcing current + physical current) := by
    rw [jointIdentity, forceIdentity]
    exact joint
  refine ⟨actualWeighted.1, actualWeighted.2.1, actualWeighted.2.2.1, ?_, jointBound, ?_⟩
  · simpa only [mul_add] using jointIntegrable
  have endpoint := General.coupled_endpoint_le_of_weighted_response
    (sizeContinuous.mono prefixSubset) (memoryContinuous.mono prefixSubset) (forcingContinuous.mono prefixSubset)
    (physicalContinuous.mono prefixSubset) (shapeContinuous.mono prefixSubset) combinedNonnegative forcingConstantNonnegative
    omegaNonnegative omegaWeight epsilonNonnegative epsilonOne weightPositive
    (rateOmega.trans ((by linarith only [omegaPositive] : omega / 2 ≤ omega).trans omegaWeight)) inside.1
    (fun current member => sizeNonnegative current (prefixSubset member))
    (fun current member => memoryNonnegative current (prefixSubset member))
    (fun current _ => forcingNonnegative current) (fun current _ => physicalNonnegative current)
    (coordinateBound time inside) (memoryBound time inside) (by simpa only [sub_zero] using jointBound)
  simp only [sub_zero, sizeInitial, memoryInitial, zero_add] at endpoint
  have shapeIntegralNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * shape current :=
    intervalIntegral.integral_nonneg inside.1 (fun current _ => mul_nonneg (Real.exp_pos _).le (by dsimp only [shape]; positivity))
  have forceIntegralNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (forcing current + physical current) :=
    intervalIntegral.integral_nonneg inside.1 (fun current _ => mul_nonneg (Real.exp_pos _).le
      (add_nonneg (forcingNonnegative current) (physicalNonnegative current)))
  have shapeCoefficientBound : 2 * combinedConstant * shapeConstant ≤ endpointConstant :=
    (le_max_left _ _).trans (le_max_right 1 _)
  have forceCoefficientBound : combinedConstant * (1 + 2 * forcingConstant) ≤ endpointConstant :=
    (le_max_right _ _).trans (le_max_right 1 _)
  have shapeScaled := mul_le_mul_of_nonneg_right shapeCoefficientBound
    (mul_nonneg omegaNonnegative shapeIntegralNonnegative)
  have forceScaled := mul_le_mul_of_nonneg_right forceCoefficientBound forceIntegralNonnegative
  have interior :
      (2 * combinedConstant * omega * shapeConstant) * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * shape current) +
        (combinedConstant * (1 + 2 * forcingConstant)) * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (forcing current + physical current)) ≤
      endpointConstant * (omega * (∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * shape current) +
        ∫ current in (0 : ℝ)..time, Real.exp (-weight * current) * (forcing current + physical current)) := by
    nlinarith only [shapeScaled, forceScaled]
  exact endpoint.2.trans ((mul_le_mul_of_nonneg_left interior (Real.exp_pos _).le).trans_eq (by ring))

end EulerNonuniqueness.Paper
