import EulerNonuniqueness.Section5.CascadeSaddleGradedLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeSaddleSourceResponse
import EulerNonuniqueness.Section5.CascadeFirstMomentLocalForeignHistory
import EulerNonuniqueness.Section5.CascadeForeignPatchCoefficientIntegrability
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section5.CascadeRelativeDilationHistory

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_cascade_saddle_graded_local_foreign_history :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 → ∃ constant ≥ (1 : ℝ),
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
      let graded := fun time => (indexedReferenceSize + dilation time + |(relative time).2|) * shape time +
        indexedReferenceSize * dilation time
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
      let upper := fun time => constant * omega * graded time + tolerance * (moment time + center time + shape time) +
        constant * omega * epsilon * (center time + raw time) +
        constant * epsilon * ∑ patch : Fin 4, foreign patch time +
        constant * (length / centerRadius) * (changed.strain * center time + difference time) +
        constant * indexedReferenceSize * ‖leading time‖
      0 < growth ∧ ContinuousOn relative (Icc 0 finish) ∧ ContinuousOn leading (Icc 0 finish) ∧
      ContinuousOn remainder (Icc 0 finish) ∧ IntervalIntegrable difference volume 0 finish ∧
      (∀ patch : Fin 4, IntervalIntegrable (foreign patch) volume 0 finish) ∧
      IntervalIntegrable upper volume 0 finish ∧ IntervalIntegrable (fun time => ‖remainder time‖) volume 0 finish ∧
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
    pointRadius, pointPositive, pointQuarter, compatible, pointCap, pointCapPositive, points⟩ :=
    exists_uniform_actual_cascade_saddle_graded_local_foreign_return
  obtain ⟨responseRadius, responsePositive, responseQuarter, responses⟩ :=
    exists_uniform_cascade_saddle_source_response (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth
  obtain ⟨duhamelRadius, duhamelPositive, duhamelQuarter, duhamels⟩ :=
    exists_uniform_cascade_saddle_original_duhamel (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth
  obtain ⟨regularRadius, regularPositive, regularQuarter, regularity⟩ :=
    exists_uniform_cascade_paired_chart_regularity (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth
  obtain ⟨momentCap, momentPositive, moments⟩ := exists_uniform_actual_firstMoment_local_foreign_history
  obtain ⟨patchCap, patchPositive, patches⟩ := exists_uniform_actual_foreign_patch_coefficient_integrability
  obtain ⟨stateCap, statePositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min pointCap (min momentCap (min patchCap stateCap))
  have capPositive : 0 < rawCap := lt_min pointCapPositive (lt_min momentPositive (lt_min patchPositive statePositive))
  have pointCapBound : rawCap ≤ pointCap := min_le_left _ _
  have momentCapBound : rawCap ≤ momentCap := (min_le_right _ _).trans (min_le_left _ _)
  have patchCapBound : rawCap ≤ patchCap := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have stateCapBound : rawCap ≤ stateCap := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  let baseRadius := min pointRadius (min responseRadius (min duhamelRadius regularRadius))
  let radius := baseRadius / 2
  have basePositive : 0 < baseRadius := lt_min pointPositive (lt_min responsePositive (lt_min duhamelPositive regularPositive))
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusBase : radius < baseRadius := by dsimp only [radius]; linarith only [basePositive]
  have basePoint : baseRadius ≤ pointRadius := min_le_left _ _
  have baseResponse : baseRadius ≤ responseRadius := (min_le_right _ _).trans (min_le_left _ _)
  have baseDuhamel : baseRadius ≤ duhamelRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have baseRegular : baseRadius ≤ regularRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    radius, radiusPositive, radiusBase.le.trans (basePoint.trans pointQuarter), compatible, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨constant, constantOne, pointParameters⟩ := points factorPositive factorSmall
  obtain ⟨momentConstant, momentNonnegative, momentParameters⟩ := moments factorPositive factorEighth
  refine ⟨constant, constantOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant
    tolerance rootOne boundaryOne thresholdBound referenceNonnegative tolerancePositive
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  filter_upwards [pointParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdBound referenceNonnegative tolerancePositive,
    responses scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    momentParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    patches scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative basePositive,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℝ)] with frequency pointEstimate responseEstimate momentEstimate patchEstimate referenceSmall lengths frequencyPositive
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
  let remainder := relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared.toCascadeMaterialPreparedPair)
    graph coordinate index
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
  let graded := fun time => (indexedReferenceSize + dilation time + |(relative time).2|) * shape time +
    indexedReferenceSize * dilation time
  let difference := fun time => ∑' power : ℕ,
    ‖quadrupoleExteriorCoefficient changed first index time centerRadius power -
      quadrupoleExteriorCoefficient changed second index time centerRadius power‖
  let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖firstFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid firstFamily.patchMotion current index patch) patchRadius (power + 1) time -
      secondFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid secondFamily.patchMotion current index patch) patchRadius (power + 1) time‖
  let upper := fun time => constant * omega * graded time + tolerance * (moment time + center time + shape time) +
    constant * omega * epsilon * (center time + raw time) + constant * epsilon * ∑ patch : Fin 4, foreign patch time +
    constant * (length / centerRadius) * (changed.strain * center time + difference time) +
    constant * indexedReferenceSize * ‖leading time‖
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| < baseRadius := by
    fin_cases side
    · exact (small time inside).trans_lt radiusBase
    · have sharp := referenceSmall prepared.toCascadeMaterialPreparedPair time
        (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩) index
      change |unstableShape second time index| + |stableShape second time index| < baseRadius
      linarith only [sharp, abs_nonneg (diagonalDifference second time index / length ^ 2 - 1)]
  obtain ⟨growthPositive, leadingContinuous, remainderContinuous, unstableIdentity, stableBound, stableWeighted⟩ :=
    responseEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index nonterminal finish finishNonnegative finishBound
      (fun time inside => (small time inside).trans (radiusBase.le.trans baseResponse))
  obtain ⟨inputContinuous, unstablePoint, stableIdentity, _, _⟩ :=
    duhamels prepared.toCascadeMaterialPreparedPair path index nonterminal finish finishNonnegative finishBound
      (fun side time inside => (pairedSmall side time inside).trans_le baseDuhamel)
  have relativeContinuous : ContinuousOn relative (Icc 0 finish) :=
    (regularity prepared.toCascadeMaterialPreparedPair path index finish finishBound
      (fun side time inside => (pairedSmall side time inside).trans_le baseRegular)).1
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) := relativeContinuous.fst.abs.add relativeContinuous.snd.abs
  have centerContinuous : ContinuousOn center (Icc 0 finish) :=
    (stateContinuity prepared capPositive stateCapBound path index).2.1.mono subset
  have rawContinuous : ContinuousOn raw (Icc 0 finish) := continuousOn_finset_sum _
    (fun patch _ => ((stateContinuity prepared capPositive stateCapBound path index).1 patch).mono subset)
  have momentContinuous : ContinuousOn moment (Icc 0 finish) := by
    apply ContinuousOn.norm
    intro time inside
    exact (path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index
      (subset inside)).continuousAt.continuousWithinAt
  have diagonalContinuous : ContinuousOn
      (fun time => diagonalDifference first time index - diagonalDifference second time index) (Icc 0 finish) := by
    intro time inside
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith only [inside.1], by linarith only [inside.2, finishBound, path.stopBound]⟩
    have derivative := (prepared.toCascadeMaterialPreparedPair.paired_diagonal_hasDerivAt 0 index globalInside).sub
      (prepared.toCascadeMaterialPreparedPair.paired_diagonal_hasDerivAt 1 index globalInside)
    simpa only [first, second, cascadePairedMotion, Fin.cases_zero, Fin.cases_succ] using
      derivative.continuousAt.continuousWithinAt (s := Icc (0 : ℝ) finish)
  have dilationContinuous : ContinuousOn dilation (Icc 0 finish) := diagonalContinuous.abs.div_const _
  have gradedContinuous : ContinuousOn graded (Icc 0 finish) :=
    (((continuousOn_const.add dilationContinuous).add relativeContinuous.snd.abs).mul shapeContinuous).add
      (continuousOn_const.mul dilationContinuous)
  let momentPrepared := prepared.enlargeCap momentCapBound
  obtain ⟨differenceI, _, _⟩ := momentEstimate count phase dipoleAngle momentPrepared path index nonterminal finish
    finishNonnegative finishBound radialSmall
  have differenceIntegrable : IntervalIntegrable difference volume 0 finish := by
    simpa only [difference, centerRadius, first, second, prepared.referenceIdentity, momentPrepared,
      CascadeSourcePreparedPair.enlargeCap] using differenceI
  let patchPrepared := prepared.enlargeCap patchCapBound
  have patchRadiusNonnegative : 0 ≤ patchRadius :=
    mul_nonneg (div_nonneg factorPositive.le (by norm_num)) (changed.length_pos _).le
  have patchRadiusSmall : patchRadius ≤ scales.location (index.val + 1) / (100000 * 96) := by
    have lengthBound := (lengths (index.val + 1)).le
    change changed.length (index.val + 1) ≤ 1 * changed.location (index.val + 1) at lengthBound
    have numeric : factor / 39321600 ≤ 1 / (100000 * 96) := by linarith only [factorSmall]
    calc
      _ ≤ (factor / 39321600) * changed.location (index.val + 1) :=
        mul_le_mul_of_nonneg_left (by simpa only [one_mul] using lengthBound) (div_nonneg factorPositive.le (by norm_num))
      _ ≤ (1 / (100000 * 96)) * changed.location (index.val + 1) :=
        mul_le_mul_of_nonneg_right numeric (changed.location_pos _).le
      _ = _ := by dsimp only [changed, Scales.location]; ring
  have foreignIntegrable (patch : Fin 4) : IntervalIntegrable (foreign patch) volume 0 finish := by
    have actual := (patchEstimate count phase dipoleAngle patchPrepared path (index, patch) patchRadius patchRadiusNonnegative
      patchRadiusSmall finish finishNonnegative finishBound 0).2.2
    simpa only [foreign, patchRadius, firstFamily, secondFamily, patchPrepared, CascadeSourcePreparedPair.enlargeCap,
      neg_zero, zero_mul, Real.exp_zero, one_mul] using actual
  have foreignSumIntegrable : IntervalIntegrable (fun time => ∑ patch, foreign patch time) volume 0 finish := by
    simpa only [Finset.sum_apply] using
      (IntervalIntegrable.sum Finset.univ (f := foreign) (fun patch _ => foreignIntegrable patch))
  have upperIntegrable : IntervalIntegrable upper volume 0 finish := by
    have gradedI := gradedContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
    have momentI := momentContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
    have centerI := centerContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
    have rawI := rawContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
    have shapeI := shapeContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
    have leadingI := leadingContinuous.norm.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
    simpa only [upper] using
      (((((gradedI.const_mul (constant * omega)).add
        (((momentI.add centerI).add shapeI).const_mul tolerance)).add
        ((centerI.add rawI).const_mul (constant * omega * epsilon))).add
        (foreignSumIntegrable.const_mul (constant * epsilon))).add
        (((centerI.const_mul changed.strain).add differenceIntegrable).const_mul (constant * (length / centerRadius)))).add
        (leadingI.const_mul (constant * indexedReferenceSize))
  have remainderIntegrable : IntervalIntegrable (fun time => ‖remainder time‖) volume 0 finish :=
    remainderContinuous.norm.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  let pointPrepared := prepared.enlargeCap pointCapBound
  have pointwise (time : ℝ) (inside : time ∈ Ioo 0 finish) : ‖remainder time‖ ≤ upper time := by
    have actual := (pointEstimate count phase dipoleAngle pointPrepared path index nonterminal time
      ⟨inside.1, inside.2.trans_le finishBound⟩
      (fun current member => (small current ⟨member.1, member.2.trans inside.2.le⟩).trans (radiusBase.le.trans basePoint))).2.2.2
    with_reducible_and_instances
      dsimp only [upper, graded, indexedReferenceSize, dilation, shape, relative, leading, remainder, omega, length,
        centerRadius, patchRadius, epsilon, center, raw, moment, difference, foreign, first, second, firstFamily, secondFamily,
        pointPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState,
        CascadeSourcePreparedPair.rawSourceShapeBudget] at actual ⊢
      exact actual
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-growth * time)) := by fun_prop
  have weightedUpperIntegrable := upperIntegrable.continuousOn_mul weightContinuous.continuousOn
  have weightedRemainderIntegrable :=
    (weightContinuous.continuousOn.mul remainderContinuous.norm).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have weightedComparison := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) finishNonnegative
    weightedRemainderIntegrable weightedUpperIntegrable
    (fun time inside => mul_le_mul_of_nonneg_left (pointwise time inside) (Real.exp_pos _).le)
  refine ⟨growthPositive, relativeContinuous, leadingContinuous, remainderContinuous, differenceIntegrable, foreignIntegrable,
    upperIntegrable, remainderIntegrable, pointwise, ?_, ?_⟩
  · intro time inside
    have subsetTime : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have unorderedSubset : uIcc (0 : ℝ) time ⊆ uIcc 0 finish := by
      rw [uIcc_of_le inside.1, uIcc_of_le finishNonnegative]
      exact subsetTime
    have normIntegralBound := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) inside.1
      (remainderIntegrable.mono_set unorderedSubset) (upperIntegrable.mono_set unorderedSubset)
      (fun current member => pointwise current ⟨member.1, member.2.trans_le inside.2⟩)
    have kernelContinuous : Continuous (fun current : ℝ => Real.exp (-growth * (time - current))) := by fun_prop
    have kernelRemainder := ((kernelContinuous.continuousOn).mul
      (((leadingContinuous.mono subsetTime).snd.abs).add (remainderContinuous.mono subsetTime).norm)).intervalIntegrable_of_Icc
        (μ := volume) inside.1
    have kernelUpper := (((leadingContinuous.snd.abs.intervalIntegrable_of_Icc (μ := volume) finishNonnegative).add
      upperIntegrable).mono_set unorderedSubset).continuousOn_mul kernelContinuous.continuousOn
    have kernelComparison := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) inside.1 kernelRemainder kernelUpper
      (fun current member => mul_le_mul_of_nonneg_left
        (add_le_add_left (pointwise current ⟨member.1, member.2.trans_le inside.2⟩) _) (Real.exp_pos _).le)
    exact ⟨normIntegralBound, unstableIdentity time inside, stableIdentity time inside,
      (stableBound time inside).trans kernelComparison⟩
  · exact stableWeighted.trans (mul_le_mul_of_nonneg_left
      (add_le_add_left weightedComparison _) (by norm_num : (0 : ℝ) ≤ 1 / 2))

end EulerNonuniqueness.Paper

