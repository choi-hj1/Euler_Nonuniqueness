import EulerNonuniqueness.Section5.CascadeSaddleGradedLocalForeignHistory
import EulerNonuniqueness.Section5.CascadeDilationIntegratedAction
import EulerNonuniqueness.Section6.ReferenceStraightenedShapeSmallness
import EulerNonuniqueness.Section1.UniformIntegratedReferenceIndexBudget
import EulerNonuniqueness.General.GradedStableIntegralAbsorption
import EulerNonuniqueness.General.StableOriginalHistoryIntegral

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_integrated_nonlinear_coefficient :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ stableConstant ≥ (1 : ℝ), ∃ dilationConstant ≥ (0 : ℝ),
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
      ∀ {scaleRoot boundaryConstant threshold referenceConstant tolerance : ℝ},
      1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ thresholdMax → 0 ≤ referenceConstant → 0 < tolerance →
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
      ContinuousOn coefficient (Icc 0 finish) ∧ ContinuousOn dilationMajorant (Icc 0 finish) ∧
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
          ∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * upper time) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    stableRadius, stableRadiusPositive, stableRadiusQuarter, compatible, stableCap, stablePositive, stableFactory⟩ :=
    exists_uniform_actual_cascade_saddle_graded_local_foreign_history
  obtain ⟨dilationCap, dilationPositive, dilationFactory⟩ := exists_uniform_actual_dilation_integrated_action
  obtain ⟨stateCap, statePositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min stableCap (min dilationCap stateCap)
  have rawPositive : 0 < rawCap := lt_min stablePositive (lt_min dilationPositive statePositive)
  have stableCapBound : rawCap ≤ stableCap := min_le_left _ _
  have dilationCapBound : rawCap ≤ dilationCap := (min_le_right _ _).trans (min_le_left _ _)
  have stateCapBound : rawCap ≤ stateCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    compatible, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, stables⟩ := stableFactory factorPositive factorSmall
  obtain ⟨dilationConstant, dilationNonnegative, dilations⟩ := dilationFactory factorPositive factorSmall
  have stablePositive : 0 < stableConstant := zero_lt_one.trans_le stableOne
  let shapeCap := 1 / (4 * stableConstant)
  have shapeCapPositive : 0 < shapeCap := by dsimp only [shapeCap]; positivity
  obtain ⟨smallRadius, smallPositive, _, chartSmall⟩ := exists_uniform_referenceStraightenedShape_difference_small
    graphAnalytic.continuousAt coordinateSmooth.continuousAt graphZero coordinateZero shapeCapPositive
  let radius := min stableRadius smallRadius
  have radiusPositive : 0 < radius := lt_min stableRadiusPositive smallPositive
  refine ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, radius, radiusPositive,
    (min_le_left _ _).trans stableRadiusQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant tolerance
    rootOne boundaryOne thresholdBound referenceNonnegative tolerancePositive
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  have budgetNonnegative : 0 ≤ stableConstant * chartConstant * referenceConstant :=
    mul_nonneg (mul_nonneg stablePositive.le (zero_le_one.trans chartOne)) referenceNonnegative
  filter_upwards [stables scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdBound referenceNonnegative tolerancePositive,
    dilations scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdSmall referenceNonnegative tolerancePositive,
    scales.eventually_cascade_foreign_coefficient_series_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative smallPositive,
    scales.eventually_uniform_reference_index_rate_small ratioBound alphaPositive budgetNonnegative
      (by norm_num : (0 : ℝ) < 1 / 4),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (1 : ℝ)] with frequency stableEstimate dilationEstimate seriesEstimate referenceSmall referenceBudget lengths frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall small
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let firstFamily := prepared.trajectory.movingFamily
  let secondFamily := prepared.referenceWitness.trajectory.movingFamily
  let relative := fun time => referenceStraightenedShape first graph coordinate index time -
    referenceStraightenedShape second graph coordinate index time
  let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time index
  let remainder := relativeStraightenedSaddleStrainRemainder changed
    (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate index
  let omega := changed.omega (index.val + 1)
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
  have centerCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext current source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rawCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have stableData := stableEstimate count phase dipoleAngle (prepared.enlargeCap stableCapBound) path index nonterminal
    finish finishNonnegative finishBound radialSmall (fun time inside => (small time inside).trans (min_le_left _ _))
  dsimp only at stableData
  simp only [centerCapInvariant, rawCapInvariant] at stableData
  obtain ⟨growthPositive, relativeContinuous, leadingContinuous, remainderContinuous, _, _, upperIntegrable,
    remainderIntegrable, remainderBound, histories, weightedStable⟩ := stableData
  change ContinuousOn relative (Icc 0 finish) at relativeContinuous
  change ContinuousOn leading (Icc 0 finish) at leadingContinuous
  change ContinuousOn remainder (Icc 0 finish) at remainderContinuous
  change IntervalIntegrable upper volume 0 finish at upperIntegrable
  have dilationData := dilationEstimate count phase dipoleAngle (prepared.enlargeCap dilationCapBound) path index nonterminal
    finish finishNonnegative finishBound radialSmall
  dsimp only at dilationData
  simp only [centerCapInvariant, rawCapInvariant] at dilationData
  have dilationContinuous : ContinuousOn dilation (Icc 0 finish) := by
    simpa only [dilation, first, second, length, prepared.referenceIdentity] using dilationData.1
  have dilationMajorantContinuous : ContinuousOn dilationMajorant (Icc 0 finish) := by
    simpa only [dilationMajorant, moment, center, raw, omega, epsilon, length, difference, foreign,
      first, second, firstFamily, secondFamily, centerRadius, patchRadius, prepared.referenceIdentity] using dilationData.2.1
  have dilationAction : omega * (∫ time in (0 : ℝ)..finish, dilation time) ≤
      omega * ∫ time in (0 : ℝ)..finish, (finish - time) * dilationMajorant time := by
    simpa only [dilation, dilationMajorant, moment, center, raw, omega, epsilon, length, difference, foreign,
      first, second, firstFamily, secondFamily, centerRadius, patchRadius, prepared.referenceIdentity] using dilationData.2.2.2.2
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive
    (by change 1 ≤ scales.ratio; linarith only [ratioBound]) (index.val + 1))
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have referenceNonnegativeActual : 0 ≤ indexedReferenceSize := by
    dsimp only [indexedReferenceSize]
    exact mul_nonneg (mul_nonneg (zero_le_one.trans chartOne) referenceNonnegative)
      (add_nonneg (div_nonneg (add_nonneg strainNonnegative (sq_nonneg _)) omegaPositive.le)
        (pow_nonneg (inv_nonneg.mpr omegaPositive.le) _))
  have referenceControl : stableConstant * indexedReferenceSize ≤ 1 / 4 := by
    have actual : omega * (stableConstant * indexedReferenceSize) ≤ 1 / 4 := by
      convert (referenceBudget (index.val + 1)).2.le using 1
      dsimp only [omega, indexedReferenceSize]
      ring
    exact (le_mul_of_one_le_left (mul_nonneg stablePositive.le referenceNonnegativeActual) omegaOne).trans actual
  have shapeControl (time : ℝ) (inside : time ∈ Icc 0 finish) : shape time ≤ shapeCap := by
    have sharp := referenceSmall prepared.toCascadeMaterialPreparedPair time
      ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩ index
    have referenceChart : |unstableShape second time index| + |stableShape second time index| ≤ smallRadius := by
      change |diagonalDifference second time index / length ^ 2 - 1| +
        |unstableShape second time index| + |stableShape second time index| < smallRadius at sharp
      linarith only [sharp, abs_nonneg (diagonalDifference second time index / length ^ 2 - 1)]
    exact chartSmall first second index time ((small time inside).trans (min_le_right _ _)) referenceChart
  have momentContinuous : ContinuousOn moment (Icc 0 finish) := by
    apply ContinuousOn.norm
    intro time inside
    exact (path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index
      (subset inside)).continuousAt.continuousWithinAt
  have stateData := stateContinuity prepared rawPositive stateCapBound path index
  have centerContinuous : ContinuousOn center (Icc 0 finish) := stateData.2.1.mono subset
  have rawContinuous : ContinuousOn raw (Icc 0 finish) :=
    continuousOn_finset_sum Finset.univ (fun patch _ => (stateData.1 patch).mono subset)
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) := relativeContinuous.fst.abs.add relativeContinuous.snd.abs
  have coefficientContinuous : ContinuousOn coefficient (Icc 0 finish) :=
    (continuousOn_const.add dilationContinuous).add relativeContinuous.snd.abs
  have locationPositive := changed.location_pos (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have scalarSmall : factor / 39321600 ≤ 1 / (100000 * 96) := by linarith only [factorSmall]
  have centerRadiusPositive : 0 < centerRadius := mul_pos (div_pos factorPositive (by norm_num)) locationPositive
  have centerSmall : centerRadius ≤ scales.location (index.val + 1) / (100000 * 96) := by
    simpa only [centerRadius, changed, div_eq_mul_inv, one_mul, mul_comm] using
      mul_le_mul_of_nonneg_right scalarSmall locationPositive.le
  have lengthBelow : length ≤ changed.location (index.val + 1) := by
    simpa only [one_mul] using (lengths (index.val + 1)).le
  have patchNonnegative : 0 ≤ patchRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) lengthPositive.le
  have patchSmall : patchRadius ≤ scales.location (index.val + 1) / (100000 * 96) :=
    (mul_le_mul_of_nonneg_left lengthBelow (div_nonneg factorPositive.le (by norm_num))).trans centerSmall
  have centerData := seriesEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index
    centerRadius centerRadiusPositive.le centerSmall
  have patchData := seriesEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index
    patchRadius patchNonnegative patchSmall
  have differenceContinuous : ContinuousOn difference (Icc 0 finish) := by
    simpa only [difference, first, second, prepared.referenceIdentity] using centerData.2.2.mono subset
  have foreignSumContinuous : ContinuousOn (fun time => ∑ patch : Fin 4, foreign patch time) (Icc 0 finish) :=
    continuousOn_finset_sum Finset.univ (fun patch _ => ((patchData.1 patch).2).mono subset)
  have forcingContinuous : ContinuousOn forcing (Icc 0 finish) :=
    (((((leadingContinuous.snd.abs.add
      (continuousOn_const.mul ((momentContinuous.add centerContinuous).add shapeContinuous))).add
      (continuousOn_const.mul (centerContinuous.add rawContinuous))).add
      (continuousOn_const.mul foreignSumContinuous)).add
      (continuousOn_const.mul ((continuousOn_const.mul centerContinuous).add differenceContinuous))).add
      (continuousOn_const.mul leadingContinuous.norm))
  have forcingNonnegative (time : ℝ) (_ : time ∈ Icc 0 finish) : 0 ≤ forcing time := by
    have centerNonnegative : 0 ≤ center time := by
      dsimp only [center, CascadeSourcePreparedPair.rawSourceCenteredState]
      exact div_nonneg (norm_nonneg _) lengthPositive.le
    have rawNonnegative : 0 ≤ raw time := by
      dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    have differenceNonnegative : 0 ≤ difference time := tsum_nonneg fun power => norm_nonneg _
    have foreignNonnegative : 0 ≤ ∑ patch : Fin 4, foreign patch time :=
      Finset.sum_nonneg fun patch _ => tsum_nonneg fun power => mul_nonneg (by positivity) (norm_nonneg _)
    have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
    dsimp only [forcing, moment, shape]
    positivity
  have forcingIntegrable := forcingContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have gradedContinuous : ContinuousOn graded (Icc 0 finish) :=
    (coefficientContinuous.mul shapeContinuous).add (continuousOn_const.mul dilationContinuous)
  have gradedIntegrable := gradedContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have stableBound : (2 * Real.sqrt 2 * omega) * (∫ time in (0 : ℝ)..finish, |(relative time).2|) ≤
      (∫ time in (0 : ℝ)..finish, forcing time) + stableConstant * omega *
        ∫ time in (0 : ℝ)..finish, graded time := by
    have stableNorm := General.stable_integral_of_original_history
      (relative := relative) (leading := leading) (remainder := remainder)
      growthPositive finishNonnegative relativeContinuous leadingContinuous remainderContinuous
      (fun time inside => (histories time inside).2.2.1)
    have actual := stableNorm.trans (add_le_add_left (histories finish ⟨finishNonnegative, le_rfl⟩).1 _)
    change (2 * Real.sqrt 2 * omega) * (∫ time in (0 : ℝ)..finish, |(relative time).2|) ≤
      (∫ time in (0 : ℝ)..finish, |(leading time).2|) + ∫ time in (0 : ℝ)..finish, upper time at actual
    apply actual.trans_eq
    rw [← intervalIntegral.integral_add
      (leadingContinuous.snd.abs.intervalIntegrable_of_Icc (μ := volume) finishNonnegative) upperIntegrable,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add forcingIntegrable (gradedIntegrable.const_mul (stableConstant * omega))]
    apply intervalIntegral.integral_congr
    intro time _
    dsimp only [upper, forcing]
    ring
  have shapeConstantSmall : stableConstant * shapeCap ≤ 1 / 4 := by
    have identity : stableConstant * (1 / (4 * stableConstant)) = (1 / 4 : ℝ) := by
      field_simp [stablePositive.ne']
      ring
    exact identity.le
  have rateBound : 2 * omega ≤ 2 * Real.sqrt 2 * omega := by
    have rootOne : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    nlinarith only [mul_le_mul_of_nonneg_right rootOne omegaPositive.le]
  have absorbed := General.graded_stable_integral_absorption finishNonnegative omegaPositive stablePositive.le
    referenceNonnegativeActual shapeCapPositive.le shapeConstantSmall referenceControl dilationContinuous
    relativeContinuous.snd.abs shapeContinuous forcingContinuous
    (fun time _ => div_nonneg (abs_nonneg _) (sq_nonneg _)) (fun time _ => abs_nonneg _)
    (fun time _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) forcingNonnegative shapeControl rateBound stableBound
  have substituted : omega * (∫ time in (0 : ℝ)..finish, coefficient time) ≤
      2 * omega * indexedReferenceSize * finish +
        2 * omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationMajorant time) +
        ∫ time in (0 : ℝ)..finish, forcing time := by
    apply absorbed.trans
    have added := add_le_add_right (add_le_add_left
      (mul_le_mul_of_nonneg_left dilationAction (by norm_num : (0 : ℝ) ≤ 2))
      (2 * omega * indexedReferenceSize * finish)) (∫ time in (0 : ℝ)..finish, forcing time)
    convert added using 1 <;> ring
  have remainingContinuous : ContinuousOn (fun time => (finish - time) * dilationMajorant time) (Icc 0 finish) :=
    (continuous_const.sub continuous_id).continuousOn.mul dilationMajorantContinuous
  exact ⟨coefficientContinuous, dilationMajorantContinuous, forcingContinuous,
    coefficientContinuous.intervalIntegrable_of_Icc finishNonnegative,
    remainingContinuous.intervalIntegrable_of_Icc finishNonnegative, forcingIntegrable, substituted,
    growthPositive, relativeContinuous, leadingContinuous, remainderContinuous, remainderIntegrable,
    upperIntegrable, remainderBound, histories, weightedStable⟩

end EulerNonuniqueness.Paper
