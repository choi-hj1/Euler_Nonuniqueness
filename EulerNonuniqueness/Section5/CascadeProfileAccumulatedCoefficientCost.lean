import EulerNonuniqueness.Section5.CascadeSaddleExactWeightRemainderComparison
import EulerNonuniqueness.Section5.CascadeGivenMapCoefficientMajorants
import EulerNonuniqueness.Section5.CascadeSelectedForeignForcingContinuity
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.General.WeightedForcingAccumulatedCost

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_profile_accumulated_coefficient_cost :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ stableConstant ≥ (1 : ℝ), ∃ dilationConstant ≥ (0 : ℝ), ∃ constant ≥ (1 : ℝ),
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
      ∀ {scaleRoot boundaryConstant threshold referenceConstant tolerance : ℝ},
      1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ thresholdMax → 0 ≤ referenceConstant → 0 < tolerance → tolerance ≤ 1 →
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
      ∀ origin magnitude action : ℝ, 0 ≤ magnitude → 0 ≤ action →
        (∀ time ∈ Icc 0 finish, state time ≤ magnitude * Real.exp (growth * (time - origin))) →
        (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * allForeign time) ≤ action * Real.exp (-growth * origin) →
        actionCost ≤ 2 * omega * indexedReferenceSize * finish +
          3 * constant * (magnitude + action) * Real.exp (growth * (finish - origin)) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth, compatible, exactCap, exactPositive, exactFactory⟩ :=
    exists_uniform_actual_cascade_saddle_exact_weight_remainder_comparison
  obtain ⟨majorantCap, majorantPositive, majorants⟩ :=
    exists_uniform_actual_given_map_coefficient_majorants graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨stateCap, statePositive, states⟩ := exists_uniform_actual_source_state_continuity
  obtain ⟨geometryRadius, geometryPositive, _, _, _, geometries⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  let rawCap := min exactCap (min majorantCap stateCap)
  have capPositive : 0 < rawCap := lt_min exactPositive (lt_min majorantPositive statePositive)
  have capExact : rawCap ≤ exactCap := min_le_left _ _
  have capMajorant : rawCap ≤ majorantCap := (min_le_right _ _).trans (min_le_left _ _)
  have capState : rawCap ≤ stateCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth, compatible, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  obtain ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, exactRadius, exactRadiusPositive, exactQuarter, exactParameters⟩ :=
    exactFactory factorPositive factorSmall
  obtain ⟨majorantRadius, majorantRadiusPositive, _, constant, constantOne, majorantParameters⟩ :=
    majorants chartConstant chartOne stableConstant (zero_le_one.trans stableOne) dilationConstant dilationNonnegative
  let radius := min exactRadius (min majorantRadius geometryRadius)
  refine ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, constant, constantOne,
    radius, lt_min exactRadiusPositive (lt_min majorantRadiusPositive geometryPositive), (min_le_left _ _).trans exactQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant tolerance
    rootOne boundaryOne thresholdBound referenceNonnegative tolerancePositive toleranceOne
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  filter_upwards [exactParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdBound referenceNonnegative tolerancePositive,
    majorantParameters factor factorPositive factorSmall scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      rootOne boundaryOne thresholdSmall referenceNonnegative tolerancePositive toleranceOne,
    geometries scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) factorPositive factorEighth thresholdSmall referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    scales.eventually_cascade_selected_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (1 : ℝ)]
    with frequency exactEstimate majorantEstimate geometryEstimate coherence foreignEstimate radii frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall small
  have rawInvariant {largerCap : ℝ} (larger : rawCap ≤ largerCap) :
      (prepared.enlargeCap larger).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have actual := exactEstimate count phase dipoleAngle (prepared.enlargeCap capExact) path index nonterminal finish finishNonnegative
    finishBound radialSmall (fun time inside => (small time inside).trans (min_le_left _ _))
  simp only [rawInvariant] at actual
  dsimp only [CascadeSourcePreparedPair.enlargeCap] at actual
  refine ⟨actual, ?_⟩
  intro suppliedLift suppliedContinuous suppliedInitial suppliedPolar
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
  let actionCost := 2 * omega * indexedReferenceSize * finish +
    2 * omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationMajorant time) +
    ∫ time in (0 : ℝ)..finish, forcing time
  let size := prepared.finiteCoordinateSize graph coordinate suppliedLift index
  let state := fun time => size time + raw time
  let allForeign := prepared.selectedForeignForcing (Finset.univ.erase index) index
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  obtain ⟨geometryLift, geometryProperties, geometryPolar, geometryContinuous, _, _, _⟩ :=
    geometryEstimate prepared path index nonterminal finish finishNonnegative finishBound
      (fun time inside => (small time inside).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have sizeEquality := (coherence prepared path index finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans ((min_le_left _ _).trans exactQuarter)) geometryLift suppliedLift
    (fun side => (geometryProperties side).1.continuousOn) suppliedContinuous
    (fun side => (geometryProperties side).2.trans (suppliedInitial side).symm) geometryPolar suppliedPolar).2.2 graph coordinate
  have sizeContinuous : ContinuousOn size (Icc 0 finish) :=
    geometryContinuous.congr (fun time inside => (sizeEquality inside).symm)
  have rawContinuous : ContinuousOn raw (Icc 0 finish) := continuousOn_finset_sum _
    (fun patch _ => ((states prepared capPositive capState path index).1 patch).mono subset)
  have stateContinuous : ContinuousOn state (Icc 0 finish) := sizeContinuous.add rawContinuous
  have foreignData := foreignEstimate count phase dipoleAngle prepared path index (Finset.univ.erase index) (fun _ member => member)
  have foreignContinuous : ContinuousOn allForeign (Icc 0 finish) := foreignData.2.1.mono subset
  have weightedContinuous : Continuous (fun time : ℝ => Real.exp (-growth * time)) := by fun_prop
  have foreignIntegrable := (weightedContinuous.continuousOn.mul foreignContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  refine ⟨stateContinuous, foreignContinuous, foreignIntegrable, ?_⟩
  intro origin magnitude action magnitudeNonnegative actionNonnegative profile weightedForcing
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaGrowth : omega ≤ growth := by
    have rootTwo : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    dsimp only [growth]; nlinarith only [omegaPositive, mul_nonneg omegaPositive.le (sub_nonneg.mpr rootTwo)]
  have growthPositive : 0 < growth := omegaPositive.trans_le omegaGrowth
  have epsilonOne : epsilon ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos (changed.length_pos _))).mpr
    exact pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le
      (by simpa only [one_mul] using (radii (index.val + 1)).le) 2
  have dilationContinuous := actual.1.1.2.1
  have forcingContinuous := actual.1.1.2.2.1
  change ContinuousOn dilationMajorant (Icc 0 finish) at dilationContinuous
  change ContinuousOn forcing (Icc 0 finish) at forcingContinuous
  have majorantData := majorantEstimate count phase dipoleAngle capMajorant prepared path index nonterminal finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans ((min_le_right _ _).trans (min_le_left _ _)))
    suppliedLift suppliedContinuous suppliedInitial suppliedPolar
  have bounds (time : ℝ) (inside : time ∈ Icc 0 finish) :
      dilationMajorant time ≤ constant * (omega * state time + allForeign time) ∧
      forcing time ≤ constant * (omega * state time + allForeign time) := by
    have pointwise := majorantData time inside
    change 0 ≤ dilationMajorant time ∧ dilationMajorant time ≤ constant * (omega * (size time + epsilon * raw time) + allForeign time) ∧
      0 ≤ forcing time ∧ forcing time ≤ constant * (omega * (size time + epsilon * raw time) + allForeign time) at pointwise
    have rawNonnegative : 0 ≤ raw time := by
      dsimp only [raw]; apply Finset.sum_nonneg; intro patch _; dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
    have budgetBound : omega * (size time + epsilon * raw time) + allForeign time ≤ omega * state time + allForeign time := by
      have scaled := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left rawNonnegative epsilonOne) omegaPositive.le
      dsimp only [state]; nlinarith only [scaled]
    have comparison := mul_le_mul_of_nonneg_left budgetBound (zero_le_one.trans constantOne)
    exact ⟨pointwise.2.1.trans comparison, pointwise.2.2.2.trans comparison⟩
  change actionCost ≤ 2 * omega * indexedReferenceSize * finish +
    3 * constant * (magnitude + action) * Real.exp (growth * (finish - origin))
  exact General.accumulated_cost_le_of_state_profile_and_weighted_forcing finishNonnegative growthPositive
    omegaPositive.le omegaGrowth (zero_le_one.trans constantOne) magnitudeNonnegative actionNonnegative
    stateContinuous foreignContinuous dilationContinuous forcingContinuous (fun time _ => foreignData.1 time)
    profile weightedForcing (fun time inside => (bounds time inside).1) (fun time inside => (bounds time inside).2)

end EulerNonuniqueness.Paper

