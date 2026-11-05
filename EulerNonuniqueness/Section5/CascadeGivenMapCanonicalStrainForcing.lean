import EulerNonuniqueness.Section5.CascadeStraightenedForcingSmallInput
import EulerNonuniqueness.Section5.CascadeActualCentroidErrorArrayLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeActualMacroCoefficientSeriesAction
import EulerNonuniqueness.Section5.CascadeReferenceIndexDecay
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

private theorem canonical_strain_forcing_scalar
    {value forcing localConstant constant omega epsilon center raw foreign scale strain difference tail referenceSize
      referenceUnstable leading sourceCoefficient small target error : ℝ}
    (forcingNonnegative : 0 ≤ forcing) (epsilonNonnegative : 0 ≤ epsilon)
    (omegaNonnegative : 0 ≤ omega) (centerNonnegative : 0 ≤ center) (rawNonnegative : 0 ≤ raw)
    (foreignNonnegative : 0 ≤ foreign) (scaleNonnegative : 0 ≤ scale) (strainNonnegative : 0 ≤ strain)
    (differenceNonnegative : 0 ≤ difference) (referenceNonnegative : 0 ≤ referenceSize)
    (leadingNonnegative : 0 ≤ leading) (sourceNonnegative : 0 ≤ sourceCoefficient)
    (localBound : 120 * forcing * localConstant ≤ constant)
    (foreignBound : 30 * forcing * localConstant ≤ constant)
    (sourceBound : 30 * forcing * (sourceCoefficient + 9) ≤ constant) (leadingBound : forcing ≤ constant)
    (smallBound : small ≤ target)
    (errorBound : error ≤ 4 * localConstant * omega * epsilon * (center + raw) + localConstant * epsilon * foreign)
    (tailBound : tail ≤ difference) (referenceBound : referenceUnstable ≤ referenceSize)
    (original : value ≤ small + 30 * forcing * error +
      30 * forcing * (scale * (sourceCoefficient * strain * center + 9 * tail)) + forcing * referenceUnstable * leading) :
    value ≤ target + constant * omega * epsilon * (center + raw) + constant * epsilon * foreign +
      constant * scale * (strain * center + difference) + constant * referenceSize * leading := by
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
  linarith only [original, errors, localTerm, foreignTerm, sourceScaled, sourceFinal, reference, leadingFinal, smallBound]

theorem exists_uniform_actual_given_map_canonical_strain_forcing
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 → ∃ constant ≥ (1 : ℝ),
    ∀ chartConstant : ℝ, 1 ≤ chartConstant → ∀ tolerance : ℝ, 0 < tolerance →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
    ∀ {scaleRoot boundaryConstant threshold referenceConstant : ℝ},
    1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ current ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion current index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion current index| ≤ radius) →
    ∀ time ∈ Icc 0 finish,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let length := changed.length (index.val + 1)
    let omega := changed.omega (index.val + 1)
    let macroRadius := factor / 39321600 * changed.location (index.val + 1)
    let ownRadius := factor / 39321600 * length
    let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
    let leading := quadrupoleRelativeLeadingStrain changed first second time index
    let relative := referenceStraightenedShape first graph coordinate index time -
      referenceStraightenedShape second graph coordinate index time
    let shape := |relative.1| + |relative.2|
    let referenceSize := chartConstant * referenceConstant *
      ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
    let blockTerms := fun power : ℕ => ‖quadrupoleExteriorCoefficient changed first index time macroRadius power -
      quadrupoleExteriorCoefficient changed second index time macroRadius power‖
    let patchTerms := fun (patch : Fin 4) (power : ℕ) => (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first current index patch) ownRadius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch)
            ownRadius (power + 1) time‖
    Summable blockTerms ∧ (∀ patch : Fin 4, Summable (patchTerms patch)) ∧
    ‖referenceStraightenedForcing changed first graph coordinate index time -
        referenceStraightenedForcing changed second graph coordinate index time - leading‖ ≤
      tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + prepared.rawSourceCenteredState time index + shape) +
      constant * omega * epsilon * (prepared.rawSourceCenteredState time index + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
      constant * epsilon * ∑ patch : Fin 4, ∑' power : ℕ, patchTerms patch power +
      constant * (length / macroRadius) * (changed.strain * prepared.rawSourceCenteredState time index + ∑' power : ℕ, blockTerms power) +
      constant * referenceSize * ‖leading‖ := by
  obtain ⟨forcingRadius, forcingPositive, forcingQuarter, forcingConstant, forcingOne, forcings⟩ :=
    exists_uniform_cascade_straightened_forcing_small_input graphSmooth coordinateSmooth graphDerivative coordinateDerivative
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverse⟩ :=
    localNormalFormChart_exists_uniform_inverse_lipschitz graphSmooth coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨localCap, localCapPositive, locals⟩ := exists_uniform_actual_centroid_error_array_local_foreign_return
  obtain ⟨sourceRadius, sourceRadiusPositive, macroCap, macroCapPositive, macroConstant, macroNonnegative, macros⟩ :=
    exists_uniform_actual_macro_coefficient_series_action
  let baseRadius := min forcingRadius inverseRadius
  let radius := baseRadius / 2
  have basePositive : 0 < baseRadius := lt_min forcingPositive inversePositive
  have radiusPositive : 0 < radius := half_pos basePositive
  have radiusBase : radius < baseRadius := by dsimp only [radius]; linarith only [basePositive]
  let rawCap := min localCap macroCap
  have localCapBound : rawCap ≤ localCap := min_le_left _ _
  have macroCapBound : rawCap ≤ macroCap := min_le_right _ _
  refine ⟨radius, radiusPositive, radiusBase.le.trans ((min_le_left _ _).trans forcingQuarter), rawCap,
    lt_min localCapPositive macroCapPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  obtain ⟨localConstant, localNonnegative, localFactory⟩ := locals factorPositive factorOne
  let sourceCoefficient := 6 * (96 / Real.pi * 2304)
  let constant := max 1 (max (120 * forcingConstant * localConstant)
    (max (30 * forcingConstant * localConstant) (max (30 * forcingConstant * (sourceCoefficient + 9)) forcingConstant)))
  have constantOne : 1 ≤ constant := le_max_left _ _
  have localBound : 120 * forcingConstant * localConstant ≤ constant := (le_max_left _ _).trans (le_max_right _ _)
  have foreignBound : 30 * forcingConstant * localConstant ≤ constant :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have sourceBound : 30 * forcingConstant * (sourceCoefficient + 9) ≤ constant :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have leadingBound : forcingConstant ≤ constant :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨constant, constantOne, ?_⟩
  intro chartConstant chartOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive orbit sectionTime
    scaleRoot boundaryConstant threshold referenceConstant rootOne boundaryOne thresholdSmall referenceNonnegative
  let pointTolerance := tolerance / (inverseConstant + 1)
  have pointPositive : 0 < pointTolerance := by dsimp only [pointTolerance]; positivity
  have pointBound : pointTolerance ≤ tolerance := div_le_self tolerancePositive.le (by linarith only [inverseOne])
  have inverseBound : pointTolerance * inverseConstant ≤ tolerance := by
    have identity : pointTolerance * (inverseConstant + 1) = tolerance := by dsimp only [pointTolerance]; field_simp
    nlinarith only [identity, pointPositive]
  filter_upwards [forcings scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdSmall
      referenceNonnegative factorPositive factorEighth pointPositive,
    localFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    macros scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne
      factorPositive factorOne,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative basePositive,
    eventually_gt_atTop (0 : ℝ)] with frequency forcingEstimate localEstimate macroEstimate referenceSmall frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound small time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  let omega := changed.omega (index.val + 1)
  let macroRadius := factor / 39321600 * changed.location (index.val + 1)
  let ownRadius := factor / 39321600 * length
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let leading := quadrupoleRelativeLeadingStrain changed first second time index
  let shape := |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
    |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2|
  let center := prepared.rawSourceCenteredState time index
  let raw := ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let referenceRaw := referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  let referenceSize := chartConstant * referenceRaw
  let blockTerms := fun power : ℕ => ‖quadrupoleExteriorCoefficient changed first index time macroRadius power -
    quadrupoleExteriorCoefficient changed second index time macroRadius power‖
  let patchTerms := fun (patch : Fin 4) (power : ℕ) => (96 : ℝ) ^ (power + 1) *
    ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first current index patch) ownRadius (power + 1) time -
      prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch)
          ownRadius (power + 1) time‖
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have unitInside : time ∈ Icc (0 : ℝ) 1 := ⟨inside.1, fullInside.2.trans path.stopBound⟩
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have lengthPositive : 0 < length := changed.length_pos _
  have macroPositive : 0 < macroRadius := mul_pos (div_pos factorPositive (by norm_num)) (changed.location_pos _)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg (fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have centerNonnegative : 0 ≤ center := div_nonneg (norm_nonneg _) lengthPositive.le
  have rawNonnegative : 0 ≤ raw := by
    apply Finset.sum_nonneg
    intro patch _
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have radial (current : ℝ) (member : current ∈ Icc 0 finish) : |radialShape first current index| ≤ 1 / 2 := by
    rw [radialShape_eq_unstable_add_stable]
    exact (abs_add _ _).trans ((small current member).trans
      ((radiusBase.le.trans ((min_le_left _ _).trans forcingQuarter)).trans (by norm_num)))
  have refSmall : |unstableShape second time index| + |stableShape second time index| < baseRadius := by
    have actual := referenceSmall prepared.toCascadeMaterialPreparedPair time unitInside index
    linarith only [actual, abs_nonneg (diagonalDifference second time index / length ^ 2 - 1)]
  have physicalBound : |unstableShape first time index - unstableShape second time index| ≤ inverseConstant * shape := by
    have actual := inverse (unstableShape first time index, stableShape first time index)
      (unstableShape second time index, stableShape second time index)
      (((small time inside).trans_lt radiusBase).trans_le (min_le_right _ _)) (refSmall.trans_le (min_le_right _ _))
    have chartNorm : ‖localNormalFormChart graph coordinate (unstableShape first time index, stableShape first time index) -
        localNormalFormChart graph coordinate (unstableShape second time index, stableShape second time index)‖ ≤ shape := by
      dsimp only [shape, referenceStraightenedShape]
      rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans
      (actual.trans (mul_le_mul_of_nonneg_left chartNorm (zero_le_one.trans inverseOne)))
  have toleranceBound : pointTolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + center +
      |unstableShape first time index - unstableShape second time index|) ≤
      tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + center + shape) := by
    have firstBound := mul_le_mul_of_nonneg_right pointBound
      (add_nonneg (norm_nonneg (relativeNormalizedFirstMoment changed first second index time)) centerNonnegative)
    have secondBound := mul_le_mul_of_nonneg_left physicalBound pointPositive.le
    have thirdBound := mul_le_mul_of_nonneg_right inverseBound (show 0 ≤ shape by dsimp only [shape]; positivity)
    nlinarith only [firstBound, secondBound, thirdBound]
  have centerCapIdentity : (prepared.enlargeCap localCapBound).rawSourceCenteredState time index = center := by
    with_reducible_and_instances
      dsimp only [center, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rawCapIdentity : (∑ patch : Fin 4, (prepared.enlargeCap localCapBound).rawSourceShapeBudget time index patch) = raw := by
    with_reducible_and_instances
      dsimp only [raw, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have localData := localEstimate count phase dipoleAngle (prepared.enlargeCap localCapBound) path fullInside index
  dsimp only at localData
  rw [centerCapIdentity, rawCapIdentity] at localData
  with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at localData
  obtain ⟨patchSummable, patchBound⟩ := localData
  obtain ⟨macroShapes, weightedSummable, _, _⟩ :=
    macroEstimate count phase dipoleAngle (prepared.enlargeCap macroCapBound) path fullInside index
  have weightedBlock : Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * blockTerms power) := by
    simpa only [blockTerms, macroRadius, first, second, CascadeSourcePreparedPair.enlargeCap,
      prepared.referenceIdentity, norm_sub_rev] using weightedSummable
  have blockSummable : Summable blockTerms := Summable.of_nonneg_of_le
    (fun power => norm_nonneg _) (fun power => le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by norm_num))) weightedBlock
  have tailBound : (∑' power : ℕ, blockTerms (power + 1)) ≤ ∑' power : ℕ, blockTerms power := by
    have identity := blockSummable.tsum_eq_zero_add
    linarith only [identity, show 0 ≤ blockTerms 0 from norm_nonneg _]
  have sharp := prepared.toCascadeMaterialPreparedPair.reference_sharp_defect_le_index_budget unitInside index
  have referenceRawNonnegative : 0 ≤ referenceRaw := by dsimp only [referenceRaw]; positivity
  have referenceBound : |unstableShape second time index| ≤ referenceSize := by
    change |diagonalDifference second time index / length ^ 2 - 1| + |unstableShape second time index| +
      |stableShape second time index| ≤ referenceRaw at sharp
    have rawBound : |unstableShape second time index| ≤ referenceRaw := by
      linarith only [sharp, abs_nonneg (diagonalDifference second time index / length ^ 2 - 1), abs_nonneg (stableShape second time index)]
    exact rawBound.trans (by simpa only [referenceSize, one_mul] using mul_le_mul_of_nonneg_right chartOne referenceRawNonnegative)
  have positionsIdentity : ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
      (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length = center := by
    dsimp only [center, CascadeSourcePreparedPair.rawSourceCenteredState, first, second, length]
    rw [prepared.referenceIdentity, norm_sub_rev]
  have actual := forcingEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index nonterminal finish
    finishNonnegative finishBound radial time inside ((small time inside).trans (radiusBase.le.trans (min_le_left _ _)))
  change _ ≤ pointTolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ +
      (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length) +
      |unstableShape first time index - unstableShape second time index|) +
    30 * forcingConstant * (‖quadrupoleDilationPatchError changed first index time - quadrupoleDilationPatchError changed second index time‖ / length) +
    30 * forcingConstant * ((length / macroRadius) * (6 * (96 / Real.pi * (2304 * changed.strain)) *
      (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length) +
      9 * (∑' power : ℕ, blockTerms (power + 1)))) + forcingConstant * |unstableShape second time index| * ‖leading‖ at actual
  rw [positionsIdentity] at actual
  have normalized : ‖referenceStraightenedForcing changed first graph coordinate index time -
      referenceStraightenedForcing changed second graph coordinate index time - leading‖ ≤
      pointTolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + center +
        |unstableShape first time index - unstableShape second time index|) +
      30 * forcingConstant * (‖quadrupoleDilationPatchError changed first index time - quadrupoleDilationPatchError changed second index time‖ / length) +
      30 * forcingConstant * ((length / macroRadius) * (sourceCoefficient * changed.strain * center +
        9 * (∑' power : ℕ, blockTerms (power + 1)))) + forcingConstant * |unstableShape second time index| * ‖leading‖ := by
    convert actual using 1
    dsimp only [sourceCoefficient]
    ring
  have errorBound : ‖quadrupoleDilationPatchError changed first index time - quadrupoleDilationPatchError changed second index time‖ / length ≤
      4 * localConstant * omega * epsilon * (center + raw) + localConstant * epsilon * ∑ patch : Fin 4, ∑' power : ℕ, patchTerms patch power := by
    with_reducible_and_instances
      dsimp only [first, second, length, omega, epsilon, patchTerms, ownRadius]
      rw [prepared.referenceIdentity]
      exact patchBound
  have foreignNonnegative : 0 ≤ ∑ patch : Fin 4, ∑' power : ℕ, patchTerms patch power :=
    Finset.sum_nonneg fun patch _ => tsum_nonneg fun _ => mul_nonneg (by positivity) (norm_nonneg _)
  have referenceNonnegative : 0 ≤ referenceSize := mul_nonneg (zero_le_one.trans chartOne) referenceRawNonnegative
  have closed := canonical_strain_forcing_scalar
    (forcing := forcingConstant) (localConstant := localConstant) (constant := constant)
    (omega := omega) (epsilon := epsilon) (center := center) (raw := raw)
    (foreign := ∑ patch : Fin 4, ∑' power : ℕ, patchTerms patch power) (scale := length / macroRadius)
    (strain := changed.strain) (difference := ∑' power : ℕ, blockTerms power) (tail := ∑' power : ℕ, blockTerms (power + 1))
    (referenceSize := referenceSize) (referenceUnstable := |unstableShape second time index|) (leading := ‖leading‖)
    (sourceCoefficient := sourceCoefficient)
    (zero_le_one.trans forcingOne) epsilonNonnegative omegaPositive.le centerNonnegative rawNonnegative
    foreignNonnegative (div_nonneg lengthPositive.le macroPositive.le) strainNonnegative (tsum_nonneg fun _ => norm_nonneg _)
    referenceNonnegative (norm_nonneg _) (by dsimp only [sourceCoefficient]; positivity)
    localBound foreignBound sourceBound leadingBound toleranceBound errorBound tailBound referenceBound normalized
  refine ⟨blockSummable, patchSummable, ?_⟩
  convert closed using 1
  dsimp only [referenceSize, referenceRaw, shape, omega, length, macroRadius, epsilon, center, raw,
    leading, first, second, patchTerms, ownRadius, blockTerms, changed]
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

end EulerNonuniqueness.Paper
