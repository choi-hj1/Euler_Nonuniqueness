import EulerNonuniqueness.Section5.CascadeSaddleGradedLeadingStrainEquation
import EulerNonuniqueness.Section5.CascadeActualCentroidErrorArrayReturn
import EulerNonuniqueness.Section5.CascadeCentroidBudgetLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeActualMacroCoefficientSeriesAction
import EulerNonuniqueness.Section6.NormalFormInverseMatching

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem graded_chart_tolerance
    {tolerance pointTolerance chart moment center unstable shape : ℝ}
    (pointNonnegative : 0 ≤ pointTolerance) (pointBound : pointTolerance ≤ tolerance)
    (chartBound : pointTolerance * chart ≤ tolerance)
    (momentNonnegative : 0 ≤ moment) (centerNonnegative : 0 ≤ center) (shapeNonnegative : 0 ≤ shape)
    (unstableBound : unstable ≤ chart * shape) :
    pointTolerance * (moment + center + unstable) ≤ tolerance * (moment + center + shape) := by
  have first := mul_le_mul_of_nonneg_right pointBound (add_nonneg momentNonnegative centerNonnegative)
  have second := mul_le_mul_of_nonneg_left unstableBound pointNonnegative
  have third := mul_le_mul_of_nonneg_right chartBound shapeNonnegative
  nlinarith only [first, second, third]

private theorem graded_local_foreign_bound
    {remainder pointConstant forcingConstant localConstant constant omega graded tolerancePart smallPart
      error epsilon center raw foreign scale strain difference tail referenceSize referenceUnstable leading sourceCoefficient : ℝ}
    (omegaNonnegative : 0 ≤ omega) (gradedNonnegative : 0 ≤ graded)
    (forcingNonnegative : 0 ≤ forcingConstant) (localNonnegative : 0 ≤ localConstant)
    (epsilonNonnegative : 0 ≤ epsilon) (centerNonnegative : 0 ≤ center) (rawNonnegative : 0 ≤ raw)
    (foreignNonnegative : 0 ≤ foreign) (scaleNonnegative : 0 ≤ scale)
    (strainNonnegative : 0 ≤ strain) (differenceNonnegative : 0 ≤ difference)
    (referenceNonnegative : 0 ≤ referenceSize) (leadingNonnegative : 0 ≤ leading)
    (sourceNonnegative : 0 ≤ sourceCoefficient)
    (pointBound : pointConstant ≤ constant)
    (localBound : 120 * forcingConstant * localConstant ≤ constant)
    (foreignBound : 30 * forcingConstant * localConstant ≤ constant)
    (sourceBound : 30 * forcingConstant * (sourceCoefficient + 9) ≤ constant)
    (leadingBound : forcingConstant ≤ constant)
    (small : smallPart ≤ tolerancePart)
    (errorBound : error ≤ 4 * localConstant * omega * epsilon * (center + raw) + localConstant * epsilon * foreign)
    (tailBound : tail ≤ difference) (referenceBound : referenceUnstable ≤ referenceSize)
    (original : remainder ≤ pointConstant * omega * graded +
      (smallPart + 30 * forcingConstant * error +
        30 * forcingConstant * (scale * (sourceCoefficient * strain * center + 9 * tail)) +
        forcingConstant * referenceUnstable * leading)) :
    remainder ≤ constant * omega * graded + tolerancePart +
      constant * omega * epsilon * (center + raw) + constant * epsilon * foreign +
      constant * scale * (strain * center + difference) + constant * referenceSize * leading := by
  have point := mul_le_mul_of_nonneg_right pointBound (mul_nonneg omegaNonnegative gradedNonnegative)
  have errors := mul_le_mul_of_nonneg_left errorBound (mul_nonneg (by norm_num : (0 : ℝ) ≤ 30) forcingNonnegative)
  have localTerm := mul_le_mul_of_nonneg_right localBound
    (mul_nonneg (mul_nonneg omegaNonnegative epsilonNonnegative) (add_nonneg centerNonnegative rawNonnegative))
  have foreignTerm := mul_le_mul_of_nonneg_right foreignBound (mul_nonneg epsilonNonnegative foreignNonnegative)
  have sourceTail := mul_le_mul_of_nonneg_left tailBound (by norm_num : (0 : ℝ) ≤ 9)
  have sourceSlackOne := mul_nonneg sourceNonnegative differenceNonnegative
  have sourceSlackTwo := mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) (mul_nonneg strainNonnegative centerNonnegative)
  have sourcePolynomial : sourceCoefficient * strain * center + 9 * tail ≤
      (sourceCoefficient + 9) * (strain * center + difference) := by
    nlinarith only [sourceTail, sourceSlackOne, sourceSlackTwo]
  have sourceScaled := mul_le_mul_of_nonneg_left sourcePolynomial
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 30) forcingNonnegative) scaleNonnegative)
  have sourceFinal := mul_le_mul_of_nonneg_right sourceBound
    (mul_nonneg scaleNonnegative (add_nonneg (mul_nonneg strainNonnegative centerNonnegative) differenceNonnegative))
  have reference := mul_le_mul_of_nonneg_left referenceBound (mul_nonneg forcingNonnegative leadingNonnegative)
  have leadingFinal := mul_le_mul_of_nonneg_right leadingBound (mul_nonneg referenceNonnegative leadingNonnegative)
  linarith only [original, point, errors, localTerm, foreignTerm, sourceScaled, sourceFinal, reference, leadingFinal, small]

theorem exists_uniform_actual_cascade_saddle_graded_local_foreign_return :
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
      ∀ index : Fin count, index.val + 1 < count → ∀ time ∈ Ioo 0 path.stop,
      (∀ current ∈ Icc 0 time,
        |unstableShape prepared.trajectory.movingFamily.patchMotion current index| +
          |stableShape prepared.trajectory.movingFamily.patchMotion current index| ≤ radius) →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let firstChart := referenceStraightenedShape first graph coordinate index time
      let secondChart := referenceStraightenedShape second graph coordinate index time
      let shape := |firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|
      let length := changed.length (index.val + 1)
      let centerRadius := factor / 39321600 * changed.location (index.val + 1)
      let patchRadius := factor / 39321600 * length
      let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
      let dilationDifference := |diagonalDifference first time index - diagonalDifference second time index| / length ^ 2
      let indexedReferenceSize := chartConstant * referenceConstant *
        ((changed.strain + changed.strain ^ 2) / changed.omega (index.val + 1) +
          (changed.omega (index.val + 1))⁻¹ ^ 5)
      let leading := quadrupoleRelativeLeadingStrain changed first second time index
      let centerTerms := fun power : ℕ =>
        ‖quadrupoleExteriorCoefficient changed first index time centerRadius power -
          quadrupoleExteriorCoefficient changed second index time centerRadius power‖
      let firstFamily := prepared.trajectory.movingFamily
      let secondFamily := prepared.referenceWitness.trajectory.movingFamily
      let patchTerms := fun (patch : Fin 4) (power : ℕ) => (96 : ℝ) ^ (power + 1) *
        ‖firstFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid firstFamily.patchMotion current index patch) patchRadius (power + 1) time -
          secondFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid secondFamily.patchMotion current index patch) patchRadius (power + 1) time‖
      HasDerivAt (fun current => referenceStraightenedShape first graph coordinate index current -
          referenceStraightenedShape second graph coordinate index current)
        ((2 * Real.sqrt 2 * changed.omega (index.val + 1) * (firstChart.1 - secondChart.1),
            -(2 * Real.sqrt 2 * changed.omega (index.val + 1)) * (firstChart.2 - secondChart.2)) +
          leading + relativeStraightenedSaddleStrainRemainder changed
            (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate index time) time ∧
      Summable centerTerms ∧ (∀ patch : Fin 4, Summable (patchTerms patch)) ∧
      ‖relativeStraightenedSaddleStrainRemainder changed
          (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate index time‖ ≤
        constant * changed.omega (index.val + 1) *
          ((indexedReferenceSize + dilationDifference + |firstChart.2 - secondChart.2|) * shape +
            indexedReferenceSize * dilationDifference) +
        tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ +
          prepared.rawSourceCenteredState time index + shape) +
        constant * changed.omega (index.val + 1) * epsilon *
          (prepared.rawSourceCenteredState time index + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
        constant * epsilon * ∑ patch : Fin 4, ∑' power : ℕ, patchTerms patch power +
        constant * (length / centerRadius) *
          (changed.strain * prepared.rawSourceCenteredState time index + ∑' power : ℕ, centerTerms power) +
        constant * indexedReferenceSize * ‖leading‖ := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, pointConstant, pointOne, forcingConstant, forcingOne,
    thresholdMax, thresholdPositive, thresholdEighth, equationRadius, equationPositive, equationQuarter, compatible, equations⟩ :=
    exists_uniform_cascade_saddle_graded_leading_strain_equation
  obtain ⟨sourceRadius, sourcePositive, returnCap, returnPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, returns⟩ := exists_uniform_actual_centroid_error_array_return
  obtain ⟨budgetCap, budgetPositive, budgets⟩ := exists_uniform_actual_centroid_budget_local_foreign_return
  obtain ⟨macroRadius, macroRadiusPositive, macroCap, macroPositive, macroConstant, macroNonnegative, macros⟩ :=
    exists_uniform_actual_macro_coefficient_series_action
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverseBound⟩ :=
    localNormalFormChart_exists_uniform_inverse_lipschitz (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  let baseRadius := min equationRadius inverseRadius
  let radius := baseRadius / 2
  have basePositive : 0 < baseRadius := lt_min equationPositive inversePositive
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusBase : radius < baseRadius := by dsimp only [radius]; linarith only [basePositive]
  have baseEquation : baseRadius ≤ equationRadius := min_le_left _ _
  have baseInverse : baseRadius ≤ inverseRadius := min_le_right _ _
  let rawCap := min returnCap (min budgetCap macroCap)
  have capPositive : 0 < rawCap := lt_min returnPositive (lt_min budgetPositive macroPositive)
  have returnCapBound : rawCap ≤ returnCap := min_le_left _ _
  have budgetCapBound : rawCap ≤ budgetCap := (min_le_right _ _).trans (min_le_left _ _)
  have macroCapBound : rawCap ≤ macroCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    radius, radiusPositive, radiusBase.le.trans (baseEquation.trans equationQuarter), compatible, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨localConstant, localNonnegative, locals⟩ := budgets factorPositive factorOne
    sourceConstant sourceNonnegative receiverConstant receiverNonnegative
  let sourceCoefficient := 6 * (96 / Real.pi * 2304)
  let constant := max pointConstant (max (120 * forcingConstant * localConstant)
    (max (30 * forcingConstant * localConstant) (max (30 * forcingConstant * (sourceCoefficient + 9)) forcingConstant)))
  have pointBound : pointConstant ≤ constant := le_max_left _ _
  have localBound : 120 * forcingConstant * localConstant ≤ constant :=
    (le_max_left _ _).trans (le_max_right _ _)
  have foreignBound : 30 * forcingConstant * localConstant ≤ constant :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have sourceBound : 30 * forcingConstant * (sourceCoefficient + 9) ≤ constant :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have leadingBound : forcingConstant ≤ constant :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨constant, pointOne.trans pointBound, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant
    tolerance rootOne boundaryOne thresholdBound referenceNonnegative tolerancePositive
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  let pointTolerance := tolerance / (inverseConstant + 1)
  have inverseNonnegative : 0 ≤ inverseConstant := zero_le_one.trans inverseOne
  have pointTolerancePositive : 0 < pointTolerance := by dsimp only [pointTolerance]; positivity
  have pointToleranceBound : pointTolerance ≤ tolerance :=
    div_le_self tolerancePositive.le (by linarith only [inverseOne])
  have pointInverseBound : pointTolerance * inverseConstant ≤ tolerance := by
    have identity : pointTolerance * (inverseConstant + 1) = tolerance := by dsimp only [pointTolerance]; field_simp
    nlinarith only [identity, pointTolerancePositive]
  filter_upwards [equations scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      factorPositive factorEighth thresholdBound referenceNonnegative pointTolerancePositive,
    returns scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive factorOne,
    locals scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    macros scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne
      factorPositive factorOne,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative basePositive,
    eventually_gt_atTop (0 : ℝ)] with frequency equationEstimate returnEstimate budgetEstimate macroEstimate referenceSmall frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal time inside small
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let firstFamily := prepared.trajectory.movingFamily
  let secondFamily := prepared.referenceWitness.trajectory.movingFamily
  let firstChart := referenceStraightenedShape first graph coordinate index time
  let secondChart := referenceStraightenedShape second graph coordinate index time
  let shape := |firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|
  let omega := changed.omega (index.val + 1)
  let length := changed.length (index.val + 1)
  let centerRadius := factor / 39321600 * changed.location (index.val + 1)
  let patchRadius := factor / 39321600 * length
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let centerState := prepared.rawSourceCenteredState time index
  let rawDifference := ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let dilationDifference := |diagonalDifference first time index - diagonalDifference second time index| / length ^ 2
  let referenceRaw := referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  let indexedReferenceSize := chartConstant * referenceConstant *
    ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  let graded := (indexedReferenceSize + dilationDifference + |firstChart.2 - secondChart.2|) * shape +
    indexedReferenceSize * dilationDifference
  let leading := quadrupoleRelativeLeadingStrain changed first second time index
  let centerTerms := fun power : ℕ => ‖quadrupoleExteriorCoefficient changed first index time centerRadius power -
    quadrupoleExteriorCoefficient changed second index time centerRadius power‖
  let centerSeries := ∑' power : ℕ, centerTerms power
  let centerTail := ∑' power : ℕ, centerTerms (power + 1)
  let patchTerms := fun (patch : Fin 4) (power : ℕ) => (96 : ℝ) ^ (power + 1) *
    ‖firstFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid firstFamily.patchMotion current index patch) patchRadius (power + 1) time -
      secondFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid secondFamily.patchMotion current index patch) patchRadius (power + 1) time‖
  let foreignSeries := fun patch => ∑' power : ℕ, patchTerms patch power
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1.le, inside.2.le⟩
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have lengthPositive : 0 < length := changed.length_pos _
  have centerRadiusPositive : 0 < centerRadius := by
    exact mul_pos (div_pos factorPositive (by norm_num)) (changed.location_pos _)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg (fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
  have centerNonnegative : 0 ≤ centerState := div_nonneg (norm_nonneg _) lengthPositive.le
  have rawNonnegative : 0 ≤ rawDifference := by
    apply Finset.sum_nonneg
    intro patch _
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have pairedSmall (side : Fin 2) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| < baseRadius := by
    fin_cases side
    · exact (small time ⟨inside.1.le, le_rfl⟩).trans_lt radiusBase
    · have sharp := referenceSmall prepared.toCascadeMaterialPreparedPair time
        (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1.le, inside.2.le.trans path.stopBound⟩) index
      change |unstableShape second time index| + |stableShape second time index| < baseRadius
      linarith only [sharp, abs_nonneg (diagonalDifference second time index / length ^ 2 - 1)]
  obtain ⟨derivative, equationBound⟩ := equationEstimate prepared.toCascadeMaterialPreparedPair path index nonterminal time inside
    (fun current member => (small current member).trans (radiusBase.le.trans baseEquation))
  let returnPrepared := prepared.enlargeCap returnCapBound
  let budgetPrepared := prepared.enlargeCap budgetCapBound
  obtain ⟨shapes, returned⟩ := returnEstimate count orbit sectionTime phase dipoleAngle returnPrepared path fullInside index
  let comparisons := fun patch => returnPrepared.sourceComparison path fullInside (finProdFinEquiv (index, patch)) (shapes patch)
  have firstCenterIdentity (patch : Fin 4) :
      (prepared.referenceWitness.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).center time =
        patchCentroid secondFamily.patchMotion time index patch :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside index patch
  have secondCenterIdentity (patch : Fin 4) :
      (prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).center time =
        patchCentroid firstFamily.patchMotion time index patch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside index patch
  have patchReturn (patch : Fin 4) : Summable (patchTerms patch) ∧
      actualCentroidComparisonBudget changed (comparisons patch) (index, patch) factor sourceConstant receiverConstant ≤
        localConstant * (centerState + rawDifference) + (localConstant / omega) * foreignSeries patch := by
    have actual := budgetEstimate count phase dipoleAngle budgetPrepared path fullInside (index, patch) (shapes patch)
    have comparisonIdentity : budgetPrepared.sourceComparison path fullInside (finProdFinEquiv (index, patch)) (shapes patch) =
        comparisons patch := by
      with_reducible_and_instances
        dsimp only [comparisons, budgetPrepared, returnPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.sourceComparison]
    have centerCapIdentity : budgetPrepared.rawSourceCenteredState time index = centerState := by
      with_reducible_and_instances
        dsimp only [centerState, budgetPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
    have rawCapIdentity : (∑ patch : Fin 4, budgetPrepared.rawSourceShapeBudget time index patch) = rawDifference := by
      with_reducible_and_instances
        dsimp only [rawDifference, budgetPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
    have termIdentity (power : ℕ) : (96 : ℝ) ^ (power + 1) *
        ‖(comparisons patch).first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (comparisons patch).firstReceiver patchRadius (power + 1) time -
          (comparisons patch).second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (comparisons patch).secondReceiver patchRadius (power + 1) time‖ = patchTerms patch power := by
      dsimp only [patchTerms, comparisons, CascadeSourcePreparedPair.sourceComparison,
        FiniteMovingPatchFamily.exteriorTaylorCoefficient, returnPrepared, CascadeSourcePreparedPair.enlargeCap,
        firstFamily, secondFamily]
      rw [firstCenterIdentity, secondCenterIdentity, norm_sub_rev]
    with_reducible_and_instances
      dsimp only at actual
      rw [comparisonIdentity, centerCapIdentity, rawCapIdentity] at actual
      change Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
          ‖(comparisons patch).first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
              (comparisons patch).firstReceiver patchRadius (power + 1) time -
            (comparisons patch).second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
              (comparisons patch).secondReceiver patchRadius (power + 1) time‖) ∧
        actualCentroidComparisonBudget changed (comparisons patch) (index, patch) factor sourceConstant receiverConstant ≤
          localConstant * (centerState + rawDifference) + (localConstant / omega) *
            (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
              ‖(comparisons patch).first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
                  (comparisons patch).firstReceiver patchRadius (power + 1) time -
                (comparisons patch).second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
                  (comparisons patch).secondReceiver patchRadius (power + 1) time‖) at actual
      simpa only [termIdentity] using actual
  have summed := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => (patchReturn patch).2)
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum] at summed
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at summed
  have multiplied := mul_le_mul_of_nonneg_left summed (mul_nonneg omegaPositive.le epsilonNonnegative)
  have errorBound : ‖quadrupoleDilationPatchError changed first index time -
      quadrupoleDilationPatchError changed second index time‖ / length ≤
      4 * localConstant * omega * epsilon * (centerState + rawDifference) +
        localConstant * epsilon * ∑ patch, foreignSeries patch := by
    have actual : ‖quadrupoleDilationPatchError changed first index time -
        quadrupoleDilationPatchError changed second index time‖ / length ≤
        omega * epsilon * ∑ patch, actualCentroidComparisonBudget changed (comparisons patch)
          (index, patch) factor sourceConstant receiverConstant := by
      with_reducible_and_instances
        dsimp only [first, second, length, omega, epsilon, comparisons, returnPrepared, CascadeSourcePreparedPair.enlargeCap] at returned ⊢
        exact returned
    have expansion : omega * epsilon *
        (4 * (localConstant * (centerState + rawDifference)) + (localConstant / omega) * ∑ patch, foreignSeries patch) =
        4 * localConstant * omega * epsilon * (centerState + rawDifference) +
          localConstant * epsilon * ∑ patch, foreignSeries patch := by
      field_simp [omegaPositive.ne']
      ring
    exact actual.trans (multiplied.trans_eq expansion)
  let macroPrepared := prepared.enlargeCap macroCapBound
  obtain ⟨macroShapes, weightedSummable, _, _⟩ := macroEstimate count phase dipoleAngle macroPrepared path fullInside index
  have weightedCenterSummable : Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * centerTerms power) := by
    simpa only [centerTerms, centerRadius, first, second, macroPrepared, CascadeSourcePreparedPair.enlargeCap,
      prepared.referenceIdentity, norm_sub_rev] using weightedSummable
  have centerSummable : Summable centerTerms := Summable.of_nonneg_of_le
    (fun power => norm_nonneg _) (fun power => le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by norm_num)))
    weightedCenterSummable
  have tailBound : centerTail ≤ centerSeries := by
    have identity := centerSummable.tsum_eq_zero_add
    change centerSeries = centerTerms 0 + centerTail at identity
    linarith only [identity, show 0 ≤ centerTerms 0 from norm_nonneg _]
  have referenceRawNonnegative : 0 ≤ referenceRaw := by dsimp only [referenceRaw]; positivity
  have referenceNonnegative : 0 ≤ indexedReferenceSize := by
    have actual := mul_nonneg (zero_le_one.trans chartOne) referenceRawNonnegative
    simpa only [indexedReferenceSize, referenceRaw, mul_assoc] using actual
  have referenceUnstableBound : |unstableShape second time index| ≤ indexedReferenceSize := by
    have sharp := prepared.toCascadeMaterialPreparedPair.reference_sharp_defect_le_index_budget
      (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1.le, inside.2.le.trans path.stopBound⟩) index
    have rawBound : |unstableShape second time index| ≤ referenceRaw := by
      change |diagonalDifference second time index / length ^ 2 - 1| + |unstableShape second time index| +
        |stableShape second time index| ≤ referenceRaw at sharp
      linarith only [sharp, abs_nonneg (diagonalDifference second time index / length ^ 2 - 1),
        abs_nonneg (stableShape second time index)]
    have enlarged := mul_le_mul_of_nonneg_right chartOne referenceRawNonnegative
    exact rawBound.trans (by simpa only [one_mul, referenceRaw, indexedReferenceSize, mul_assoc] using enlarged)
  have unstableBound : |unstableShape first time index - unstableShape second time index| ≤ inverseConstant * shape := by
    have actual := inverseBound
      (unstableShape first time index, stableShape first time index)
      (unstableShape second time index, stableShape second time index)
      ((pairedSmall 0).trans_le baseInverse) ((pairedSmall 1).trans_le baseInverse)
    have normBound : ‖localNormalFormChart graph coordinate (unstableShape first time index, stableShape first time index) -
        localNormalFormChart graph coordinate (unstableShape second time index, stableShape second time index)‖ ≤ shape := by
      dsimp only [shape, firstChart, secondChart, referenceStraightenedShape]
      rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans
      (actual.trans (mul_le_mul_of_nonneg_left normBound inverseNonnegative))
  have toleranceBound := graded_chart_tolerance
    (moment := ‖relativeNormalizedFirstMoment changed first second index time‖) (center := centerState) (shape := shape)
    pointTolerancePositive.le pointToleranceBound pointInverseBound (norm_nonneg _) centerNonnegative
    (add_nonneg (abs_nonneg _) (abs_nonneg _)) unstableBound
  have gradedNonnegative : 0 ≤ graded := by dsimp only [graded, dilationDifference, shape]; positivity
  have foreignNonnegative : 0 ≤ ∑ patch, foreignSeries patch :=
    Finset.sum_nonneg (fun patch _ => tsum_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _)))
  have normalizedEquation : ‖relativeStraightenedSaddleStrainRemainder changed
      (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate index time‖ ≤
      pointConstant * omega * graded +
        (pointTolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + centerState +
          |unstableShape first time index - unstableShape second time index|) +
        30 * forcingConstant * (‖quadrupoleDilationPatchError changed first index time -
          quadrupoleDilationPatchError changed second index time‖ / length) +
        30 * forcingConstant * ((length / centerRadius) * (sourceCoefficient * changed.strain * centerState + 9 * centerTail)) +
        forcingConstant * |unstableShape second time index| * ‖leading‖) := by
    have centerIdentity : ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length = centerState := by
      dsimp only [centerState, CascadeSourcePreparedPair.rawSourceCenteredState, first, second, length]
      rw [prepared.referenceIdentity, norm_sub_rev]
    change _ ≤ pointConstant * |omega| * graded +
      (pointTolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ +
          (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
            (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length) +
          |unstableShape first time index - unstableShape second time index|) +
        30 * forcingConstant * (‖quadrupoleDilationPatchError changed first index time -
          quadrupoleDilationPatchError changed second index time‖ / length) +
        30 * forcingConstant * ((length / centerRadius) *
          (6 * (96 / Real.pi * (2304 * changed.strain)) *
            (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
              (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length) + 9 * centerTail)) +
        forcingConstant * |unstableShape second time index| * ‖leading‖) at equationBound
    rw [centerIdentity, abs_of_pos omegaPositive] at equationBound
    convert equationBound using 1 <;> dsimp only [sourceCoefficient] <;> ring
  refine ⟨derivative, centerSummable, fun patch => (patchReturn patch).1, ?_⟩
  exact graded_local_foreign_bound omegaPositive.le gradedNonnegative (zero_le_one.trans forcingOne) localNonnegative
    epsilonNonnegative centerNonnegative rawNonnegative foreignNonnegative (div_nonneg lengthPositive.le centerRadiusPositive.le)
    strainNonnegative (tsum_nonneg (fun _ => norm_nonneg _)) referenceNonnegative (norm_nonneg _)
    (by dsimp only [sourceCoefficient]; positivity) pointBound localBound foreignBound sourceBound leadingBound
    toleranceBound errorBound tailBound referenceUnstableBound normalizedEquation

end EulerNonuniqueness.Paper

