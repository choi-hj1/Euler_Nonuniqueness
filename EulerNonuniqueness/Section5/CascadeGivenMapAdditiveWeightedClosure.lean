import EulerNonuniqueness.Section5.CascadeGivenMapAdditiveSmallness
import EulerNonuniqueness.Section5.CascadeMixedForeignPatchClosedWeightedBudget
import EulerNonuniqueness.Section5.CascadeMixedAllForeignClosedWeightedForcing
import EulerNonuniqueness.Section5.CascadeLeadingStrainContinuity
import EulerNonuniqueness.Section5.CascadePairedChartRegularity

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem additive_weighted_closure_scalar {additive state own difference leading allValue ownBudget fullBudget accuracy : ℝ}
    (accuracyPositive : 0 < accuracy)
    (pointwise : additive ≤ (accuracy / 3) * (state + own + difference + leading))
    (ownBound : own ≤ ownBudget + state) (differenceBound : difference + leading ≤ allValue)
    (allBound : allValue ≤ state + fullBudget) :
    additive ≤ accuracy * state + (accuracy / 3) * (ownBudget + fullBudget) := by
  have deltaNonnegative : 0 ≤ accuracy / 3 := (div_pos accuracyPositive (by norm_num : (0 : ℝ) < 3)).le
  have scaledOwn := mul_le_mul_of_nonneg_left ownBound deltaNonnegative
  have scaledDifference := mul_le_mul_of_nonneg_left (differenceBound.trans allBound) deltaNonnegative
  nlinarith only [pointwise, scaledOwn, scaledDifference]

theorem exists_uniform_actual_given_map_additive_weighted_closure_factor_uniform
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ coarseConstant ≥ (0 : ℝ), ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∃ commonIncoming ≥ (0 : ℝ), ∃ commonOutgoing ≥ (0 : ℝ),
    ∃ fullCommonIncoming ≥ (0 : ℝ), ∃ fullCommonOutgoing ≥ (0 : ℝ),
    ∃ fullSharpIncoming ≥ (0 : ℝ), ∃ fullSharpOutgoing ≥ (0 : ℝ),
    ∃ toleranceMax : ℝ → ℝ → ℝ,
    (∀ stableConstant ≥ (0 : ℝ), ∀ accuracy > (0 : ℝ), 0 < toleranceMax stableConstant accuracy) ∧
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ responseE ≥ (1 : ℝ), ∃ fullFollower ≥ (1 : ℝ),
    ∃ ratioMin ≥ (2 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ stableConstant ≥ (0 : ℝ), ∀ accuracy > (0 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → ∀ extent : ℝ, 1 ≤ extent →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant chartConstant tolerance : ℝ),
    1 ≤ boundaryConstant → 0 ≤ chartConstant → 0 ≤ tolerance → tolerance ≤ toleranceMax stableConstant accuracy →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ receiver : Fin count, receiver.val + 1 < count →
    ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ path.stop →
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, receiver.val < source.val →
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
    (∀ source : Fin count, receiver.val < source.val → ∀ time ∈ Icc 0 (entry source),
      (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
          extent * changed.length (source.val + 1)) ∧
      (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
        extent * changed.length (source.val + 1))) →
    ∀ coefficient : ℝ, 0 < coefficient → ∀ magnitude : Fin count → ℝ,
    let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    (∀ source : Fin count, receiver.val < source.val → 0 ≤ magnitude source ∧
      ∀ time ∈ Icc 0 (entry source), sharpState source time ≤
        magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    ∀ finish ∈ Icc 0 terminal,
    (∀ time ∈ Icc 0 finish, |radialShape motion time receiver| ≤ 1 / 2) →
    (∀ current : Fin count, current.val ≤ receiver.val → ∀ time ∈ Icc 0 finish,
      |unstableShape motion time current| + |stableShape motion time current| ≤ radius) →
    ∀ suppliedLift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (suppliedLift side) (Icc 0 finish)) →
    (∀ side, suppliedLift side 0 = phase (receiver.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
          Complex.exp (Complex.I * (suppliedLift side time : ℂ))) →
    let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    (∀ source : Fin count, receiver.val < source.val → 2 * weight ≤ coefficient * changed.omega (source.val + 1)) →
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    let ownForcing := fun time => ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid motion current receiver patch) ownRadius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) ownRadius (power + 1) time‖
    let first := motion
    let second := prepared.reference
    let omega := changed.omega (receiver.val + 1)
    let length := changed.length (receiver.val + 1)
    let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
    let epsilon := changed.radius (receiver.val + 1) ^ 2 / length ^ 2
    let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
    let relative := fun time => referenceStraightenedShape first graph coordinate receiver time - referenceStraightenedShape second graph coordinate receiver time
    let shape := fun time => |(relative time).1| + |(relative time).2|
    let moment := fun time => ‖relativeNormalizedFirstMoment changed first second receiver time‖
    let center := fun time => prepared.rawSourceCenteredState time receiver
    let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
    let dilation := fun time => |diagonalDifference first time receiver - diagonalDifference second time receiver| / length ^ 2
    let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time receiver
    let difference := fun time => ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first receiver time macroRadius power -
      quadrupoleExteriorCoefficient changed second receiver time macroRadius power‖
    let forcing := fun time => |(leading time).2| + tolerance * (moment time + center time + shape time) +
      stableConstant * omega * epsilon * (center time + raw time) + stableConstant * epsilon * ownForcing time +
      stableConstant * (length / macroRadius) * (changed.strain * center time + difference time) + stableConstant * referenceSize * ‖leading time‖
    let additive := fun time => tolerance * (moment time + center time + shape time) +
      stableConstant * omega * epsilon * (center time + raw time) + stableConstant * epsilon * ownForcing time +
      stableConstant * (length / macroRadius) * (changed.strain * center time + difference time) +
      stableConstant * referenceSize * ‖leading time‖ + stableConstant * omega * referenceSize * dilation time
    let drive := fun time => ‖leading time‖ + (forcing time - |(leading time).2| + stableConstant * omega * referenceSize * dilation time)
    let stateBudget := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time + raw time
    let sourceBudget :=
      prepared.mixedSelectedFinerSourcePrefixBudget receiver incomingConstant outgoingConstant extent coefficient entry initialDistance magnitude weight finish +
      (4 * coarseConstant * responseE * (216360000 * changed.hessian + 576 * changed.strain) /
        (weight * changed.location (receiver.val + 1) ^ 4)) *
        prepared.mixedFollowerSourcePrefixBudget receiver commonIncoming commonOutgoing extent coefficient entry initialDistance magnitude weight finish +
      8 * prepared.mixedSelectedFinerSourcePrefixBudget receiver fullSharpIncoming fullSharpOutgoing extent coefficient entry initialDistance magnitude weight finish +
      (32 * fullFollower * (216360000 * changed.hessian + 576 * changed.strain) /
        (omega * changed.location (receiver.val + 1) ^ 4)) *
        prepared.mixedFollowerSourcePrefixBudget receiver fullCommonIncoming fullCommonOutgoing extent coefficient entry initialDistance magnitude weight finish
    (∀ time : ℝ, additive time = drive time - ‖leading time‖) ∧
    (∀ time ∈ Icc 0 finish, 0 ≤ additive time) ∧ ContinuousOn additive (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * additive time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * stateBudget time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * additive time) ≤
      accuracy * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * stateBudget time) + (accuracy / 3) * sourceBudget := by
  classical
  obtain ⟨addRadius, addPositive, addQuarter, additives⟩ := exists_uniform_actual_given_map_additive_smallness
    graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨ownThreshold, ownPositive, ownEighth, ownCap, ownCapPositive, coarseConstant, coarseNonnegative,
    ownIncoming, ownIncomingNonnegative, ownOutgoing, ownOutgoingNonnegative, commonIncoming, commonIncomingNonnegative,
    commonOutgoing, commonOutgoingNonnegative, owns⟩ := exists_uniform_actual_mixed_foreign_patch_closed_weighted_budget
      graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨fullThreshold, fullPositive, _, fullCap, fullCapPositive, fullCommonIncoming, fullCommonIncomingNonnegative,
    fullCommonOutgoing, fullCommonOutgoingNonnegative, fullSharpIncoming, fullSharpIncomingNonnegative, fullSharpOutgoing,
    fullSharpOutgoingNonnegative, fulls⟩ := exists_uniform_actual_mixed_all_foreign_closed_weighted_forcing
      graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨chartRadius, chartPositive, _, charts⟩ := exists_uniform_cascade_paired_chart_regularity (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth
  obtain ⟨stateCap, stateCapPositive, states⟩ := exists_uniform_actual_source_state_continuity
  let thresholdMax := min ownThreshold fullThreshold
  let rawCap := min ownCap (min fullCap stateCap)
  have capPositive : 0 < rawCap := lt_min ownCapPositive (lt_min fullCapPositive stateCapPositive)
  have ownCapBound : rawCap ≤ ownCap := min_le_left _ _
  have fullCapBound : rawCap ≤ fullCap := (min_le_right _ _).trans (min_le_left _ _)
  have stateCapBound : rawCap ≤ stateCap := (min_le_right _ _).trans (min_le_right _ _)
  let toleranceMax := fun (stableConstant accuracy : ℝ) =>
    if admissible : 0 ≤ stableConstant ∧ 0 < accuracy then
      Classical.choose (additives stableConstant admissible.1 (accuracy / 3)
        (div_pos admissible.2 (by norm_num : (0 : ℝ) < 3)))
    else 1
  have tolerancePositive (stableConstant : ℝ) (stableNonnegative : 0 ≤ stableConstant)
      (accuracy : ℝ) (accuracyPositive : 0 < accuracy) : 0 < toleranceMax stableConstant accuracy := by
    dsimp only [toleranceMax]
    rw [dif_pos ⟨stableNonnegative, accuracyPositive⟩]
    exact (Classical.choose_spec (additives stableConstant stableNonnegative (accuracy / 3)
      (div_pos accuracyPositive (by norm_num : (0 : ℝ) < 3)))).1
  refine ⟨thresholdMax, lt_min ownPositive fullPositive, (min_le_left _ _).trans ownEighth, rawCap, capPositive,
    coarseConstant, coarseNonnegative, ownIncoming, ownIncomingNonnegative, ownOutgoing, ownOutgoingNonnegative,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    fullCommonIncoming, fullCommonIncomingNonnegative, fullCommonOutgoing, fullCommonOutgoingNonnegative,
    fullSharpIncoming, fullSharpIncomingNonnegative, fullSharpOutgoing, fullSharpOutgoingNonnegative,
    toleranceMax, tolerancePositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨ownRadius, ownRadiusPositive, _, responseE, responseEOne, responseK, responseKOne, ownRoot, ownRootEight, ownFactory⟩ := owns factor factorPositive factorSmall
  obtain ⟨fullRadius, fullRadiusPositive, _, fullFollower, fullFollowerOne, fullRatio, fullRatioBound, fullRoot, fullRootEight, fullFactory⟩ := fulls factor factorPositive factorSmall
  let radius := min addRadius (min ownRadius (min fullRadius (chartRadius / 2)))
  let ratioMin := max fullRatio (max 2 (max (2 * responseE) (4 * responseK)))
  let rootMin := max ownRoot fullRoot
  have radiusAdd : radius ≤ addRadius := min_le_left _ _
  have radiusOwn : radius ≤ ownRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusFull : radius ≤ fullRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have radiusChart : radius < chartRadius := ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (by linarith only [chartPositive])
  refine ⟨radius, lt_min addPositive (lt_min ownRadiusPositive (lt_min fullRadiusPositive (half_pos chartPositive))), radiusAdd.trans addQuarter,
    responseE, responseEOne, fullFollower, fullFollowerOne, ratioMin,
    (le_max_left (2 : ℝ) _).trans (le_max_right _ _), rootMin, ownRootEight.trans (le_max_left _ _), ?_⟩
  intro stableConstant stableNonnegative accuracy accuracyPositive
  have deltaPositive : 0 < accuracy / 3 := div_pos accuracyPositive (by norm_num)
  have additiveData := Classical.choose_spec (additives stableConstant stableNonnegative (accuracy / 3) deltaPositive)
  have toleranceIdentity : toleranceMax stableConstant accuracy =
      Classical.choose (additives stableConstant stableNonnegative (accuracy / 3) deltaPositive) := by
    dsimp only [toleranceMax]
    rw [dif_pos ⟨stableNonnegative, accuracyPositive⟩]
  have additiveFactory := additiveData.2
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive extent extentOne referenceConstant referenceNonnegative referenceAmplitude
    threshold thresholdBound orbit sectionTime boundaryConstant chartConstant tolerance boundaryOne chartNonnegative toleranceNonnegative toleranceSmall
  rw [toleranceIdentity] at toleranceSmall
  have ownRootLarge : ownRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have fullRootLarge : fullRoot ≤ scaleRoot := (le_max_right _ _).trans rootLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (ownRootEight.trans ownRootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have ownRatio : max 2 (max (2 * responseE) (4 * responseK)) ≤ scales.ratio := (le_max_right _ _).trans ratioLarge
  have fullRatioLarge : fullRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ownRatio
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  have thresholdEighth : threshold ≤ 1 / 8 := thresholdBound.trans ((min_le_left _ _).trans ownEighth)
  filter_upwards [ownFactory extent extentOne 1 (by norm_num) scales scaleRoot ownRootLarge amplitudeIdentity ownRatio alphaPositive
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans (min_le_left _ _)) orbit sectionTime boundaryConstant boundaryOne,
    fullFactory scales scaleRoot fullRootLarge amplitudeIdentity fullRatioLarge alphaPositive extent extentOne referenceConstant referenceNonnegative referenceAmplitude
      threshold (thresholdBound.trans (min_le_right _ _)) orbit sectionTime boundaryConstant 1 boundaryOne (by norm_num),
    additiveFactory factor factorPositive factorEighth scales amplitudePositive ratioBound alphaPositive
      (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne) thresholdEighth referenceNonnegative chartNonnegative toleranceNonnegative toleranceSmall,
    scales.eventually_cascade_foreign_coefficient_series_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdEighth referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_relative_leading_strain_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdEighth referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative chartPositive,
    eventually_ge_atTop (1 : ℝ)] with frequency ownEstimate fullEstimate additiveEstimate series leadingEstimate referenceSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal terminal terminalNonnegative terminalBound entry initialDistance direction
  dsimp only
  intro entries extents coefficient coefficientPositive magnitude profiles finish finishInside radialSmall small suppliedLift suppliedContinuous suppliedInitial suppliedPolar
  intro rateBounds
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let omega := changed.omega (receiver.val + 1)
  let weight := 2 * Real.sqrt 2 * omega
  let length := changed.length (receiver.val + 1)
  let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
  let epsilon := changed.radius (receiver.val + 1) ^ 2 / length ^ 2
  let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  let relative := fun time => referenceStraightenedShape first graph coordinate receiver time - referenceStraightenedShape second graph coordinate receiver time
  let shape := fun time => |(relative time).1| + |(relative time).2|
  let moment := fun time => ‖relativeNormalizedFirstMoment changed first second receiver time‖
  let center := fun time => prepared.rawSourceCenteredState time receiver
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
  let dilation := fun time => |diagonalDifference first time receiver - diagonalDifference second time receiver| / length ^ 2
  let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time receiver
  let difference := fun time => ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first receiver time macroRadius power - quadrupoleExteriorCoefficient changed second receiver time macroRadius power‖
  let own := fun time => ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        (fun current => patchCentroid first current receiver patch) (factor / 39321600 * length) (power + 1) time -
      prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) (factor / 39321600 * length) (power + 1) time‖
  let state := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time + raw time
  let additive := fun time => tolerance * (moment time + center time + shape time) + stableConstant * omega * epsilon * (center time + raw time) +
    stableConstant * epsilon * own time + stableConstant * (length / macroRadius) * (changed.strain * center time + difference time) +
    stableConstant * referenceSize * ‖leading time‖ + stableConstant * omega * referenceSize * dilation time
  let allForcing := prepared.selectedForeignForcing (Finset.univ.erase receiver) receiver
  let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let ownBudget := prepared.mixedSelectedFinerSourcePrefixBudget receiver ownIncoming ownOutgoing extent coefficient entry initialDistance magnitude weight finish +
    (4 * coarseConstant * responseE * rho / (weight * changed.location (receiver.val + 1) ^ 4)) *
      prepared.mixedFollowerSourcePrefixBudget receiver commonIncoming commonOutgoing extent coefficient entry initialDistance magnitude weight finish
  let fullBudget := 8 * prepared.mixedSelectedFinerSourcePrefixBudget receiver fullSharpIncoming fullSharpOutgoing extent coefficient entry initialDistance magnitude weight finish +
    (32 * fullFollower * rho / (omega * changed.location (receiver.val + 1) ^ 4)) *
      prepared.mixedFollowerSourcePrefixBudget receiver fullCommonIncoming fullCommonOutgoing extent coefficient entry initialDistance magnitude weight finish
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have sqrtOne : 1 ≤ Real.sqrt 2 := by nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have weightLower : 2 * omega ≤ weight := mul_le_mul_of_nonneg_right (by linarith only [sqrtOne] : 2 ≤ 2 * Real.sqrt 2) omegaPositive.le
  have omegaWeight : omega ≤ weight := (le_mul_of_one_le_left omegaPositive.le (by norm_num : (1 : ℝ) ≤ 2)).trans weightLower
  have weightPositive : 0 < weight := omegaPositive.trans_le omegaWeight
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl (finishInside.2.trans terminalBound)
  have rawInvariant {larger : ℝ} (bound : rawCap ≤ larger) : (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch; with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centerInvariant {larger : ℝ} (bound : rawCap ≤ larger) : (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext time source; with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have sizeInvariant {larger : ℝ} (bound : rawCap ≤ larger) : (prepared.enlargeCap bound).finiteCoordinateSize = prepared.finiteCoordinateSize := by
    funext graph coordinate lift index time; with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.finiteCoordinateSize]
  have selectedInvariant {larger : ℝ} (bound : rawCap ≤ larger) : (prepared.enlargeCap bound).selectedForeignForcing = prepared.selectedForeignForcing := by
    funext selected index time
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.selectedForeignForcing,
      CascadeSourcePreparedPair.coarserBlockCoefficientTerm, CascadeSourcePreparedPair.coarserPatchCoefficientTerm]
  have sharpBudgetInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).mixedSelectedFinerSourcePrefixBudget = prepared.mixedSelectedFinerSourcePrefixBudget := by
    funext index incoming outgoing extent coefficient entry initialDistance magnitude weight finish
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.mixedSelectedFinerSourcePrefixBudget]
  have commonBudgetInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).mixedFollowerSourcePrefixBudget = prepared.mixedFollowerSourcePrefixBudget := by
    funext index incoming outgoing extent coefficient entry initialDistance magnitude weight finish
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.mixedFollowerSourcePrefixBudget]
  have ownData := ownEstimate count phase dipoleAngle (prepared.enlargeCap ownCapBound) path receiver nonterminal terminal terminalNonnegative terminalBound
    entry initialDistance direction entries extents coefficient coefficientPositive magnitude (by simpa only [rawInvariant, centerInvariant] using profiles)
    finish finishInside (fun current below time inside => (small current below time inside).trans radiusOwn) suppliedLift suppliedContinuous suppliedInitial suppliedPolar weight weightLower rateBounds
  dsimp only at ownData
  simp only [sizeInvariant, rawInvariant, sharpBudgetInvariant] at ownData
  with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at ownData
  obtain ⟨ownContinuous, stateContinuous, ownI, stateI, ownBound⟩ := ownData
  have fullData := fullEstimate count phase dipoleAngle (prepared.enlargeCap fullCapBound) path receiver nonterminal terminal terminalNonnegative terminalBound
    entry initialDistance direction entries extents coefficient coefficientPositive magnitude (by simpa only [rawInvariant, centerInvariant] using profiles)
    finish finishInside radialSmall (fun time inside => (small receiver le_rfl time inside).trans radiusFull)
    (fun current below time inside => (small current below.le time inside).trans radiusFull) weight omegaWeight rateBounds
  dsimp only at fullData
  simp only [selectedInvariant, sharpBudgetInvariant, commonBudgetInvariant] at fullData
  with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at fullData
  obtain ⟨allContinuous, _, _, allI, allPointwise, allBound⟩ := fullData
  have additivePointwise (time : ℝ) (inside : time ∈ Icc 0 finish) : 0 ≤ additive time ∧
      additive time ≤ (accuracy / 3) * (state time + own time + difference time + ‖leading time‖) :=
    additiveEstimate prepared path receiver nonterminal finish finishInside.1 (finishInside.2.trans terminalBound)
      (fun time inside => (small receiver le_rfl time inside).trans radiusAdd) suppliedLift suppliedContinuous suppliedInitial suppliedPolar time inside
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver| < chartRadius := by
    fin_cases side
    · exact (small receiver le_rfl time inside).trans_lt radiusChart
    · have actual := referenceSmall prepared.toCascadeMaterialPreparedPair time ⟨inside.1, inside.2.trans (finishInside.2.trans (terminalBound.trans path.stopBound))⟩ receiver
      change |unstableShape second time receiver| + |stableShape second time receiver| < chartRadius
      linarith only [actual, abs_nonneg (diagonalDifference second time receiver / length ^ 2 - 1)]
  have relativeContinuous := (charts prepared.toCascadeMaterialPreparedPair path receiver finish (finishInside.2.trans terminalBound) pairedSmall).1
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) := relativeContinuous.fst.abs.add relativeContinuous.snd.abs
  have momentContinuous : ContinuousOn moment (Icc 0 finish) := fun time inside =>
    (path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive receiver (subset inside)).continuousAt.norm.continuousWithinAt
  have centerContinuous : ContinuousOn center (Icc 0 finish) := ((states prepared capPositive stateCapBound path receiver).2.1).mono subset
  have rawContinuous : ContinuousOn raw (Icc 0 finish) := continuousOn_finset_sum Finset.univ (fun patch _ => ((states prepared capPositive stateCapBound path receiver).1 patch).mono subset)
  have diagonalContinuous : ContinuousOn (fun time => diagonalDifference first time receiver - diagonalDifference second time receiver) (Icc 0 finish) := by
    intro time inside
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith only [inside.1], by linarith only [inside.2, finishInside.2, terminalBound, path.stopBound]⟩
    have actual := (prepared.toCascadeMaterialPreparedPair.paired_diagonal_hasDerivAt 0 receiver globalInside).sub
      (prepared.toCascadeMaterialPreparedPair.paired_diagonal_hasDerivAt 1 receiver globalInside)
    simpa only [first, second, cascadePairedMotion, Fin.cases_zero, Fin.cases_succ] using actual.continuousAt.continuousWithinAt (s := Icc (0 : ℝ) finish)
  have dilationContinuous : ContinuousOn dilation (Icc 0 finish) := diagonalContinuous.abs.div_const _
  have leadingContinuous := (leadingEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver).mono subset
  have macroNonnegative : 0 ≤ macroRadius := mul_nonneg (by positivity) (changed.location_pos _).le
  have macroSmall : macroRadius ≤ scales.location (receiver.val + 1) / (100000 * 96) := by
    change factor / 39321600 * changed.location (receiver.val + 1) ≤ changed.location (receiver.val + 1) / (100000 * 96)
    nlinarith only [mul_le_mul_of_nonneg_right factorOne (changed.location_pos (receiver.val + 1)).le, changed.location_pos (receiver.val + 1)]
  have seriesData := series count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver macroRadius macroNonnegative macroSmall
  have differenceContinuous : ContinuousOn difference (Icc 0 finish) := by
    have actual := seriesData.2.2.mono subset
    simpa only [difference, first, second, prepared.referenceIdentity] using actual
  have ownContinuous' := ownContinuous.mono subset
  have additiveContinuous : ContinuousOn additive (Icc 0 finish) :=
    (((((continuousOn_const.mul ((momentContinuous.add centerContinuous).add shapeContinuous)).add
      (continuousOn_const.mul (centerContinuous.add rawContinuous))).add (continuousOn_const.mul ownContinuous')).add
      (continuousOn_const.mul ((continuousOn_const.mul centerContinuous).add differenceContinuous))).add
      (continuousOn_const.mul leadingContinuous.norm)).add (continuousOn_const.mul dilationContinuous)
  have exponential : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have additiveI := (exponential.continuousOn.mul additiveContinuous).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have differenceI := (exponential.continuousOn.mul differenceContinuous).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have leadingI := (exponential.continuousOn.mul leadingContinuous.norm).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have shapeI := (exponential.continuousOn.mul shapeContinuous).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have shapeState (time : ℝ) (inside : time ∈ Icc 0 finish) : shape time ≤ state time := by
    have lengthPositive := changed.length_pos (receiver.val + 1)
    have locationPositive := changed.location_pos (receiver.val + 1)
    have extra : 0 ≤ dilation time +
        |relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) receiver time| +
        moment time + ‖quadrupoleCenter first time receiver - quadrupoleCenter second time receiver‖ / changed.location (receiver.val + 1) + raw time := by
      have rawNonnegative : 0 ≤ raw time := by dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
      dsimp only [dilation, moment]; positivity
    calc
      _ ≤ shape time + (dilation time + |relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift
          (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) receiver time| + moment time +
          ‖quadrupoleCenter first time receiver - quadrupoleCenter second time receiver‖ / changed.location (receiver.val + 1) + raw time) := le_add_of_nonneg_right extra
      _ = state time := by dsimp only [state, shape, relative, dilation, moment, CascadeSourcePreparedPair.finiteCoordinateSize, first, second, changed, length, Prod.fst_sub, Prod.snd_sub]; ring
  have shapeActionBound : weighted shape ≤ weighted state := intervalIntegral.integral_mono_on finishInside.1 shapeI stateI
    (fun time inside => mul_le_mul_of_nonneg_left (shapeState time inside) (Real.exp_pos (-weight * time)).le)
  have principalPointwise (time : ℝ) (inside : time ∈ Icc 0 finish) : difference time + ‖leading time‖ ≤ allForcing time := by
    have restNonnegative (radius : ℝ) : 0 ≤ ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
            (fun current => patchCentroid first current receiver patch) radius (power + 1) time -
          prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
            (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) radius (power + 1) time‖ :=
      Finset.sum_nonneg fun _ _ => tsum_nonneg fun _ => mul_nonneg (by positivity) (norm_nonneg _)
    have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have externalNonnegative : 0 ≤ (∑ patch : Fin 4, ‖biotSavart (externalPatchVorticity changed first time receiver) (patchCentroid first time receiver patch) -
      biotSavart (externalPatchVorticity changed second time receiver) (patchCentroid second time receiver patch)‖) / (4 * changed.location (receiver.val + 1)) :=
      div_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (mul_nonneg (by norm_num) (changed.location_pos _).le)
    have gBound : difference time + ‖leading time‖ ≤ prepared.finiteCoordinateForeignForcing receiver time := by
      have extra := add_nonneg (add_nonneg (mul_nonneg epsilonNonnegative (restNonnegative macroRadius))
        (mul_nonneg epsilonNonnegative (restNonnegative (factor / 39321600 * length)))) externalNonnegative
      have identity : prepared.finiteCoordinateForeignForcing receiver time = ‖leading time‖ + difference time +
        epsilon * (∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid first current receiver patch) macroRadius (power + 1) time - prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) macroRadius (power + 1) time‖) +
        epsilon * own time + (∑ patch : Fin 4, ‖biotSavart (externalPatchVorticity changed first time receiver) (patchCentroid first time receiver patch) -
          biotSavart (externalPatchVorticity changed second time receiver) (patchCentroid second time receiver patch)‖) / (4 * changed.location (receiver.val + 1)) := by
        dsimp only [CascadeSourcePreparedPair.finiteCoordinateForeignForcing, leading, difference, epsilon, own, first, second, changed, macroRadius, length]
        rw [prepared.referenceIdentity]
      rw [identity]
      linarith only [extra]
    have actual := allPointwise time inside
    change prepared.finiteCoordinateForeignForcing receiver time + prepared.physicalForeignSourceForcing receiver time ≤ allForcing time at actual
    exact (gBound.trans (le_add_of_nonneg_right (prepared.physicalForeignSourceForcing_nonneg receiver time))).trans actual
  have principalActionBound : weighted difference + weighted (fun time => ‖leading time‖) ≤ weighted allForcing := by
    have actual := intervalIntegral.integral_mono_on finishInside.1 (differenceI.add leadingI) allI (by
      intro time inside; have scaled := mul_le_mul_of_nonneg_left (principalPointwise time inside) (Real.exp_pos (-weight * time)).le
      convert scaled using 1; ring)
    simpa only [intervalIntegral.integral_add differenceI leadingI] using actual
  have pointwiseActionBound : weighted additive ≤ (accuracy / 3) * (weighted state + weighted own + weighted difference + weighted (fun time => ‖leading time‖)) := by
    have actual := intervalIntegral.integral_mono_on finishInside.1 additiveI (((stateI.add ownI).add differenceI).add leadingI |>.const_mul (accuracy / 3)) (by
      intro time inside; have scaled := mul_le_mul_of_nonneg_left (additivePointwise time inside).2 (Real.exp_pos (-weight * time)).le
      convert scaled using 1; ring)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add ((stateI.add ownI).add differenceI) leadingI,
      intervalIntegral.integral_add (stateI.add ownI) differenceI, intervalIntegral.integral_add stateI ownI] at actual
    exact actual
  change weighted own ≤ ownBudget + 1 * weighted state at ownBound
  simp only [one_mul] at ownBound
  have fullNormalized : weighted allForcing ≤ weighted shape + fullBudget := by
    simpa only [weighted, allForcing, fullBudget, shape, relative, first, second, changed, omega, rho,
      prepared.referenceIdentity, Prod.fst_sub, Prod.snd_sub, one_mul, add_assoc] using allBound
  have fullActionBound : weighted allForcing ≤ weighted state + fullBudget := fullNormalized.trans (add_le_add_right shapeActionBound fullBudget)
  have result := additive_weighted_closure_scalar accuracyPositive pointwiseActionBound ownBound principalActionBound fullActionBound
  refine ⟨?_, fun time inside => (additivePointwise time inside).1, additiveContinuous, additiveI, stateI, ?_⟩
  · intro time; ring
  · convert result using 1
    dsimp only [ownBudget, fullBudget]
    ring

theorem exists_uniform_actual_given_map_additive_weighted_closure
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ coarseConstant ≥ (0 : ℝ), ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∃ commonIncoming ≥ (0 : ℝ), ∃ commonOutgoing ≥ (0 : ℝ),
    ∃ fullCommonIncoming ≥ (0 : ℝ), ∃ fullCommonOutgoing ≥ (0 : ℝ),
    ∃ fullSharpIncoming ≥ (0 : ℝ), ∃ fullSharpOutgoing ≥ (0 : ℝ),
    ∀ stableConstant ≥ (0 : ℝ), ∀ accuracy > (0 : ℝ), ∃ toleranceMax > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ responseE ≥ (1 : ℝ), ∃ fullFollower ≥ (1 : ℝ),
    ∃ ratioMin ≥ (2 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → ∀ extent : ℝ, 1 ≤ extent →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant chartConstant tolerance : ℝ),
    1 ≤ boundaryConstant → 0 ≤ chartConstant → 0 ≤ tolerance → tolerance ≤ toleranceMax →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ receiver : Fin count, receiver.val + 1 < count →
    ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ path.stop →
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, receiver.val < source.val →
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
    (∀ source : Fin count, receiver.val < source.val → ∀ time ∈ Icc 0 (entry source),
      (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
          extent * changed.length (source.val + 1)) ∧
      (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
        extent * changed.length (source.val + 1))) →
    ∀ coefficient : ℝ, 0 < coefficient → ∀ magnitude : Fin count → ℝ,
    let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    (∀ source : Fin count, receiver.val < source.val → 0 ≤ magnitude source ∧
      ∀ time ∈ Icc 0 (entry source), sharpState source time ≤
        magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    ∀ finish ∈ Icc 0 terminal,
    (∀ time ∈ Icc 0 finish, |radialShape motion time receiver| ≤ 1 / 2) →
    (∀ current : Fin count, current.val ≤ receiver.val → ∀ time ∈ Icc 0 finish,
      |unstableShape motion time current| + |stableShape motion time current| ≤ radius) →
    ∀ suppliedLift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (suppliedLift side) (Icc 0 finish)) →
    (∀ side, suppliedLift side 0 = phase (receiver.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
          Complex.exp (Complex.I * (suppliedLift side time : ℂ))) →
    let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    (∀ source : Fin count, receiver.val < source.val → 2 * weight ≤ coefficient * changed.omega (source.val + 1)) →
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    let ownForcing := fun time => ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid motion current receiver patch) ownRadius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) ownRadius (power + 1) time‖
    let first := motion
    let second := prepared.reference
    let omega := changed.omega (receiver.val + 1)
    let length := changed.length (receiver.val + 1)
    let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
    let epsilon := changed.radius (receiver.val + 1) ^ 2 / length ^ 2
    let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
    let relative := fun time => referenceStraightenedShape first graph coordinate receiver time - referenceStraightenedShape second graph coordinate receiver time
    let shape := fun time => |(relative time).1| + |(relative time).2|
    let moment := fun time => ‖relativeNormalizedFirstMoment changed first second receiver time‖
    let center := fun time => prepared.rawSourceCenteredState time receiver
    let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
    let dilation := fun time => |diagonalDifference first time receiver - diagonalDifference second time receiver| / length ^ 2
    let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time receiver
    let difference := fun time => ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first receiver time macroRadius power -
      quadrupoleExteriorCoefficient changed second receiver time macroRadius power‖
    let forcing := fun time => |(leading time).2| + tolerance * (moment time + center time + shape time) +
      stableConstant * omega * epsilon * (center time + raw time) + stableConstant * epsilon * ownForcing time +
      stableConstant * (length / macroRadius) * (changed.strain * center time + difference time) + stableConstant * referenceSize * ‖leading time‖
    let additive := fun time => tolerance * (moment time + center time + shape time) +
      stableConstant * omega * epsilon * (center time + raw time) + stableConstant * epsilon * ownForcing time +
      stableConstant * (length / macroRadius) * (changed.strain * center time + difference time) +
      stableConstant * referenceSize * ‖leading time‖ + stableConstant * omega * referenceSize * dilation time
    let drive := fun time => ‖leading time‖ + (forcing time - |(leading time).2| + stableConstant * omega * referenceSize * dilation time)
    let stateBudget := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time + raw time
    let sourceBudget :=
      prepared.mixedSelectedFinerSourcePrefixBudget receiver incomingConstant outgoingConstant extent coefficient entry initialDistance magnitude weight finish +
      (4 * coarseConstant * responseE * (216360000 * changed.hessian + 576 * changed.strain) /
        (weight * changed.location (receiver.val + 1) ^ 4)) *
        prepared.mixedFollowerSourcePrefixBudget receiver commonIncoming commonOutgoing extent coefficient entry initialDistance magnitude weight finish +
      8 * prepared.mixedSelectedFinerSourcePrefixBudget receiver fullSharpIncoming fullSharpOutgoing extent coefficient entry initialDistance magnitude weight finish +
      (32 * fullFollower * (216360000 * changed.hessian + 576 * changed.strain) /
        (omega * changed.location (receiver.val + 1) ^ 4)) *
        prepared.mixedFollowerSourcePrefixBudget receiver fullCommonIncoming fullCommonOutgoing extent coefficient entry initialDistance magnitude weight finish
    (∀ time : ℝ, additive time = drive time - ‖leading time‖) ∧
    (∀ time ∈ Icc 0 finish, 0 ≤ additive time) ∧ ContinuousOn additive (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * additive time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * stateBudget time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * additive time) ≤
      accuracy * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * stateBudget time) + (accuracy / 3) * sourceBudget := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    coarseConstant, coarseNonnegative, incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    fullCommonIncoming, fullCommonIncomingNonnegative, fullCommonOutgoing, fullCommonOutgoingNonnegative,
    fullSharpIncoming, fullSharpIncomingNonnegative, fullSharpOutgoing, fullSharpOutgoingNonnegative,
    toleranceMax, tolerancePositive, factors⟩ :=
    exists_uniform_actual_given_map_additive_weighted_closure_factor_uniform graphAnalytic coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    coarseConstant, coarseNonnegative, incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    fullCommonIncoming, fullCommonIncomingNonnegative, fullCommonOutgoing, fullCommonOutgoingNonnegative,
    fullSharpIncoming, fullSharpIncomingNonnegative, fullSharpOutgoing, fullSharpOutgoingNonnegative, ?_⟩
  intro stableConstant stableNonnegative accuracy accuracyPositive
  refine ⟨toleranceMax stableConstant accuracy, tolerancePositive stableConstant stableNonnegative accuracy accuracyPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, responseE, responseEOne, fullFollower, fullFollowerOne,
    ratioMin, ratioTwo, rootMin, rootEight, factory⟩ := factors factor factorPositive factorSmall
  exact ⟨radius, radiusPositive, radiusQuarter, responseE, responseEOne, fullFollower, fullFollowerOne,
    ratioMin, ratioTwo, rootMin, rootEight, factory stableConstant stableNonnegative accuracy accuracyPositive⟩

end EulerNonuniqueness.Paper

