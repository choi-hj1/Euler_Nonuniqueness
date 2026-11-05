import EulerNonuniqueness.Section5.CascadeCoarseSourceResponse
import EulerNonuniqueness.Section5.CascadeFiniteCoordinateChartComparison
import EulerNonuniqueness.Section5.CascadeSharpStateFiniteCoordinateBound

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_actual_given_map_coarse_source_response
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
    ∃ comparisonConstant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant boundaryConstant : ℝ,
    threshold ≤ thresholdMax → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∃ lift : Fin 2 → ℝ → ℝ,
      (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift side time : ℂ))) ∧
      let size := prepared.finiteCoordinateSize graph coordinate lift index
      let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
      let forcing := prepared.finiteCoordinateForeignForcing index
      let physical := prepared.physicalForeignSourceForcing index
      let rate := constant * ({scales with frequency := frequency} : Scales).omega (index.val + 1)
      ContinuousOn size (Icc 0 finish) ∧ ContinuousOn raw (Icc 0 finish) ∧
      ContinuousOn forcing (Icc 0 finish) ∧ ContinuousOn physical (Icc 0 finish) ∧
      IntervalIntegrable size volume 0 finish ∧ IntervalIntegrable raw volume 0 finish ∧
      IntervalIntegrable forcing volume 0 finish ∧ IntervalIntegrable physical volume 0 finish ∧
      size 0 = 0 ∧ ∀ time ∈ Icc 0 finish,
        IntervalIntegrable (fun current => Real.exp (rate * (time - current)) *
          (forcing current + physical current)) volume 0 time ∧
        size time + raw time ≤ (comparisonConstant * constant) * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (forcing current + physical current) := by
  obtain ⟨baseGraph, baseCoordinate, baseGraphAnalytic, baseGraphZero, baseGraphDerivative,
    baseCoordinateSmooth, baseCoordinateZero, baseCoordinateDerivative, thresholdMax, thresholdPositive,
    thresholdEighth, rawCap, rawPositive, baseFactory⟩ := exists_uniform_actual_coarse_source_response
  obtain ⟨comparisonRadius, comparisonPositive, _, comparisonConstant, comparisonOne, comparison⟩ :=
    exists_uniform_actual_finite_coordinate_chart_comparison baseGraphAnalytic baseCoordinateSmooth
      baseGraphZero baseCoordinateZero baseGraphDerivative baseCoordinateDerivative graphAnalytic coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨outputRadius, outputPositive, _, _, _, outputFactory⟩ :=
    exists_uniform_actual_sharp_state_finite_coordinate_bound graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨baseRadius, basePositive, baseQuarter, constant, constantOne, rootMin, rootEight, responses⟩ :=
    baseFactory factorPositive factorSmall
  let radius := min baseRadius (min outputRadius (comparisonRadius / 2))
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusBase : radius ≤ baseRadius := min_le_left _ _
  have radiusOutput : radius ≤ outputRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusComparison : radius < comparisonRadius :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  refine ⟨radius, radiusPositive, radiusBase.trans baseQuarter, constant, constantOne,
    comparisonConstant, comparisonOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
    thresholdBound referenceNonnegative boundaryOne orbit sectionTime
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  filter_upwards [responses scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant
      boundaryConstant thresholdBound referenceNonnegative boundaryOne orbit sectionTime,
    outputFactory scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) factorPositive (factorSmall.trans (by norm_num)) thresholdSmall referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative comparisonPositive]
    with frequency baseResponse outputGeometry referenceSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound small
  obtain ⟨lift, liftProperties, liftPolar, data⟩ := baseResponse count phase dipoleAngle prepared path index nonterminal
    finish finishNonnegative finishBound (fun time inside => (small time inside).trans radiusBase)
  dsimp only at data
  obtain ⟨_, rawContinuous, forcingContinuous, physicalContinuous, _, rawIntegrable,
    forcingIntegrable, physicalIntegrable, _, response⟩ := data
  have outputData := outputGeometry prepared path index nonterminal finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans radiusOutput) lift
    (fun side => (liftProperties side).1.continuousOn) (fun side => (liftProperties side).2) liftPolar
  let changed : Scales := {scales with frequency := frequency}
  let size := prepared.finiteCoordinateSize graph coordinate lift index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let forcing := prepared.finiteCoordinateForeignForcing index
  let physical := prepared.physicalForeignSourceForcing index
  let rate := constant * changed.omega (index.val + 1)
  have sizeContinuous : ContinuousOn size (Icc 0 finish) := outputData.1
  have sizeInitial : size 0 = 0 := outputData.2.1
  refine ⟨lift, liftProperties, liftPolar, sizeContinuous, rawContinuous, forcingContinuous, physicalContinuous,
    sizeContinuous.intervalIntegrable_of_Icc finishNonnegative, rawIntegrable, forcingIntegrable, physicalIntegrable,
    sizeInitial, ?_⟩
  intro time inside
  have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have kernelContinuous : Continuous (fun current : ℝ => Real.exp (rate * (time - current))) := by fun_prop
  have kernelIntegrable : IntervalIntegrable (fun current => Real.exp (rate * (time - current)) *
      (forcing current + physical current)) volume 0 time :=
    (kernelContinuous.continuousOn.mul ((forcingContinuous.add physicalContinuous).mono subset)).intervalIntegrable_of_Icc inside.1
  have referenceChart := referenceSmall prepared.toCascadeMaterialPreparedPair time
    ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩ index
  have referenceInside : |unstableShape prepared.reference time index| +
      |stableShape prepared.reference time index| < comparisonRadius := by
    linarith [abs_nonneg (diagonalDifference prepared.reference time index / changed.length (index.val + 1) ^ 2 - 1)]
  have coordinateBound := (comparison prepared lift index time
    ((small time inside).trans_lt radiusComparison) referenceInside).2
  have scaledResponse := mul_le_mul_of_nonneg_left (response time inside) (zero_le_one.trans comparisonOne)
  refine ⟨kernelIntegrable, coordinateBound.trans ?_⟩
  simpa only [mul_assoc] using scaledResponse

end EulerNonuniqueness.Paper
