import EulerNonuniqueness.Section5.CascadeSaddleExactRateUpperComparison

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_cascade_saddle_exact_weight_remainder_comparison :
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
      let drive := fun time => ‖leading time‖ + (forcing time - |(leading time).2|) +
        stableConstant * omega * indexedReferenceSize * dilation time
      let actionCost := 2 * omega * indexedReferenceSize * finish +
        2 * omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationMajorant time) +
        ∫ time in (0 : ℝ)..finish, forcing time
      let additive := fun time => drive time - ‖leading time‖
      let error := fun time => 2 * stableConstant * actionCost * Real.exp (2 * stableConstant * actionCost) *
        (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * drive current) +
        ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * additive current
      ((ContinuousOn coefficient (Icc 0 finish) ∧ ContinuousOn dilationMajorant (Icc 0 finish) ∧
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
          Real.exp (-growth * time) * (relative time).1 := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    compatible, rawCap, rawPositive, factories⟩ := exists_uniform_actual_cascade_saddle_exact_rate_upper_comparison
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    compatible, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, radius, radiusPositive, radiusQuarter, parameters⟩ :=
    factories factorPositive factorSmall
  refine ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, radius, radiusPositive, radiusQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant tolerance
    rootOne boundaryOne thresholdBound referenceNonnegative tolerancePositive
  filter_upwards [parameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
    thresholdBound referenceNonnegative tolerancePositive, eventually_ge_atTop (1 : ℝ)] with frequency estimates frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall small
  dsimp only
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
  have data := estimates count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall small
  dsimp only at data
  refine ⟨data, ?_⟩
  obtain ⟨coefficientData, driveContinuous, _, upperCompare⟩ := data
  obtain ⟨coefficientContinuous, _, _, coefficientIntegrable, _, _, actionBound, _, relativeContinuous,
    leadingContinuous, remainderContinuous, _, _, remainderBound, histories, _⟩ := coefficientData
  change ContinuousOn coefficient (Icc 0 finish) at coefficientContinuous
  change IntervalIntegrable coefficient volume 0 finish at coefficientIntegrable
  change ContinuousOn drive (Icc 0 finish) at driveContinuous
  change ContinuousOn relative (Icc 0 finish) at relativeContinuous
  change ContinuousOn leading (Icc 0 finish) at leadingContinuous
  change ContinuousOn remainder (Icc 0 finish) at remainderContinuous
  change omega * (∫ time in (0 : ℝ)..finish, coefficient time) ≤ actionCost at actionBound
  have additiveContinuous : ContinuousOn additive (Icc 0 finish) := driveContinuous.sub leadingContinuous.norm
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) := relativeContinuous.fst.abs.add relativeContinuous.snd.abs
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have lengthPositive : 0 < length := changed.length_pos _
  have locationPositive := changed.location_pos (index.val + 1)
  have stableNonnegative : 0 ≤ stableConstant := zero_le_one.trans stableOne
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have referenceNonnegativeActual : 0 ≤ indexedReferenceSize := by
    dsimp only [indexedReferenceSize]
    exact mul_nonneg (mul_nonneg (zero_le_one.trans chartOne) referenceNonnegative)
      (add_nonneg (div_nonneg (add_nonneg strainNonnegative (sq_nonneg _)) omegaPositive.le)
        (pow_nonneg (inv_nonneg.mpr omegaPositive.le) _))
  have dilationNonnegativeActual (time : ℝ) : 0 ≤ dilation time := div_nonneg (abs_nonneg _) (sq_nonneg _)
  have coefficientNonnegative (time : ℝ) : 0 ≤ coefficient time :=
    add_nonneg (add_nonneg referenceNonnegativeActual (dilationNonnegativeActual time)) (abs_nonneg _)
  have additiveNonnegative (time : ℝ) : 0 ≤ additive time := by
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
    have centerRadiusPositive : 0 < centerRadius := mul_pos (div_pos factorPositive (by norm_num)) locationPositive
    have identity : additive time = tolerance * (moment time + center time + shape time) +
        stableConstant * omega * epsilon * (center time + raw time) +
        stableConstant * epsilon * ∑ patch : Fin 4, foreign patch time +
        stableConstant * (length / centerRadius) * (changed.strain * center time + difference time) +
        stableConstant * indexedReferenceSize * ‖leading time‖ +
        stableConstant * omega * indexedReferenceSize * dilation time := by
      dsimp only [additive, drive, forcing]
      ring
    rw [identity]
    dsimp only [moment, shape]
    positivity
  have driveNonnegative (time : ℝ) : 0 ≤ drive time := by
    have identity : drive time = ‖leading time‖ + additive time := by dsimp only [additive]; ring
    rw [identity]
    exact add_nonneg (norm_nonneg _) (additiveNonnegative time)
  have exponential : Continuous (fun current : ℝ => Real.exp (-growth * current)) := by fun_prop
  let feedback := fun current => stableConstant * omega * coefficient current *
    (Real.exp (-growth * current) * shape current)
  have feedbackContinuous : ContinuousOn feedback (Icc 0 finish) :=
    (continuousOn_const.mul coefficientContinuous).mul (exponential.continuousOn.mul shapeContinuous)
  have weightedAdditiveContinuous : ContinuousOn
      (fun current => Real.exp (-growth * current) * additive current) (Icc 0 finish) :=
    exponential.continuousOn.mul additiveContinuous
  refine ⟨additiveContinuous, additiveContinuous.intervalIntegrable_of_Icc finishNonnegative, ?_⟩
  intro time inside
  have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have driveIntegrable := (upperCompare time inside).1
  change IntervalIntegrable (fun current => Real.exp (-growth * current) * drive current) volume 0 time at driveIntegrable
  have remainderIntegrable := (exponential.continuousOn.mul (remainderContinuous.norm.mono subset)).intervalIntegrable_of_Icc
    (μ := volume) inside.1
  have additiveIntegrable := (weightedAdditiveContinuous.mono subset).intervalIntegrable_of_Icc (μ := volume) inside.1
  have leadingIntegrable := (exponential.continuousOn.mul (leadingContinuous.fst.mono subset)).intervalIntegrable_of_Icc
    (μ := volume) inside.1
  have signedRemainderIntegrable := (exponential.continuousOn.mul (remainderContinuous.fst.mono subset)).intervalIntegrable_of_Icc
    (μ := volume) inside.1
  have feedbackIntegrable := (feedbackContinuous.mono subset).intervalIntegrable_of_Icc (μ := volume) inside.1
  let driveMass := ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * drive current
  let shapeBound := 2 * Real.exp (2 * stableConstant * actionCost) * driveMass
  have driveMassNonnegative : 0 ≤ driveMass :=
    intervalIntegral.integral_nonneg inside.1 (fun current _ => mul_nonneg (Real.exp_pos _).le (driveNonnegative current))
  have shapeBoundNonnegative : 0 ≤ shapeBound := mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) driveMassNonnegative
  have uniformShape (current : ℝ) (member : current ∈ Icc 0 time) :
      Real.exp (-growth * current) * shape current ≤ shapeBound := by
    have fullMember : current ∈ Icc 0 finish := subset member
    have actual := (upperCompare current fullMember).2.2
    change Real.exp (-growth * current) * shape current ≤
      2 * Real.exp (2 * stableConstant * actionCost) *
        ∫ earlier in (0 : ℝ)..current, Real.exp (-growth * earlier) * drive earlier at actual
    have drivePrefix : (∫ earlier in (0 : ℝ)..current, Real.exp (-growth * earlier) * drive earlier) ≤ driveMass := by
      apply intervalIntegral.integral_mono_interval le_rfl member.1 member.2
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with earlier _
        exact mul_nonneg (Real.exp_pos _).le (driveNonnegative earlier)
      · exact driveIntegrable
    exact actual.trans (mul_le_mul_of_nonneg_left drivePrefix (mul_nonneg (by norm_num) (Real.exp_pos _).le))
  have remainderComparison := intervalIntegral.integral_mono_on_of_le_Ioo inside.1 remainderIntegrable
    (feedbackIntegrable.add additiveIntegrable) (by
      intro current member
      have actual := mul_le_mul_of_nonneg_left
        (remainderBound current ⟨member.1, member.2.trans_le inside.2⟩) (Real.exp_pos (-growth * current)).le
      have identity : Real.exp (-growth * current) * upper current =
          feedback current + Real.exp (-growth * current) * additive current := by
        dsimp only [upper, feedback, additive, drive, forcing, graded]
        ring
      exact actual.trans_eq identity)
  rw [intervalIntegral.integral_add feedbackIntegrable additiveIntegrable] at remainderComparison
  have upperFeedbackContinuous : ContinuousOn
      (fun current => stableConstant * omega * coefficient current * shapeBound) (Icc 0 time) :=
    (continuousOn_const.mul (coefficientContinuous.mono subset)).mul continuousOn_const
  have feedbackComparison := intervalIntegral.integral_mono_on inside.1 feedbackIntegrable
    (upperFeedbackContinuous.intervalIntegrable_of_Icc (μ := volume) inside.1) (by
      intro current member
      exact mul_le_mul_of_nonneg_left (uniformShape current member)
        (mul_nonneg (mul_nonneg stableNonnegative omegaPositive.le) (coefficientNonnegative current)))
  have coefficientPrefix : (∫ current in (0 : ℝ)..time, coefficient current) ≤
      ∫ current in (0 : ℝ)..finish, coefficient current := by
    apply intervalIntegral.integral_mono_interval le_rfl inside.1 inside.2
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with current _
      exact coefficientNonnegative current
    · exact coefficientIntegrable
  have actionPrefix := (mul_le_mul_of_nonneg_left coefficientPrefix omegaPositive.le).trans actionBound
  have feedbackBound : (∫ current in (0 : ℝ)..time, feedback current) ≤
      stableConstant * shapeBound * actionCost := by
    apply feedbackComparison.trans
    calc
      (∫ current in (0 : ℝ)..time, stableConstant * omega * coefficient current * shapeBound) =
          (stableConstant * omega * shapeBound) * ∫ current in (0 : ℝ)..time, coefficient current := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro current _
        ring
      _ = stableConstant * shapeBound * (omega * ∫ current in (0 : ℝ)..time, coefficient current) := by ring
      _ ≤ stableConstant * shapeBound * actionCost :=
        mul_le_mul_of_nonneg_left actionPrefix (mul_nonneg stableNonnegative shapeBoundNonnegative)
  have errorBound : (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * ‖remainder current‖) ≤ error time := by
    apply remainderComparison.trans
    have bound := add_le_add_right feedbackBound
      (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * additive current)
    convert bound using 1
    dsimp only [error, shapeBound, driveMass]
    ring
  have signedRemainderLower : -(∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * ‖remainder current‖) ≤
      ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (remainder current).1 := by
    have comparison := intervalIntegral.integral_mono_on inside.1 remainderIntegrable.neg signedRemainderIntegrable (by
      intro current _
      have projection : |(remainder current).1| ≤ ‖remainder current‖ := by
        simpa only [Real.norm_eq_abs] using norm_fst_le (remainder current)
      have actual := mul_le_mul_of_nonneg_left (abs_le.mp projection).1 (Real.exp_pos (-growth * current)).le
      simpa only [mul_neg] using actual)
    change (∫ current in (0 : ℝ)..time, -(Real.exp (-growth * current) * ‖remainder current‖)) ≤
      (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (remainder current).1) at comparison
    simpa only [intervalIntegral.integral_neg] using comparison
  have signedLower : (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (leading current).1) - error time ≤
      Real.exp (-growth * time) * (relative time).1 := by
    have lower := add_le_add_left ((neg_le_neg errorBound).trans signedRemainderLower)
      (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (leading current).1)
    rw [← (histories time inside).2.1] at lower
    simpa only [sub_eq_add_neg] using lower
  exact ⟨remainderIntegrable, additiveIntegrable, leadingIntegrable, errorBound, signedLower⟩

end EulerNonuniqueness.Paper
