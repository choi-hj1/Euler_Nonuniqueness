import EulerNonuniqueness.Section5.CascadeDomainShapeProfileImprovement
import EulerNonuniqueness.Section5.CascadePairedChartRegularity
import EulerNonuniqueness.Section5.CascadeRelativeChartInitial

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_domain_shape_profile_bootstrap :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ),
      ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ stableConstant ≥ (1 : ℝ), ∃ profileConstant ≥ (1 : ℝ),
      ∃ costMagnitude ≥ (1 : ℝ), ∃ leadingMagnitude ≥ (1 : ℝ), ∃ additiveMagnitude ≥ (0 : ℝ),
      let accuracy := 1 / (64 * (1 + profileConstant))
      let profileMagnitude := 1 + 16 * (leadingMagnitude + accuracy * profileConstant * costMagnitude +
        (accuracy / 3) * additiveMagnitude)
      1 ≤ profileMagnitude ∧
      ∃ rootMin ≥ (8 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ endpointSize > (0 : ℝ),
      ∀ extent magnitudeMax distanceMax sourceRate : ℝ,
      1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < sourceRate →
      ∃ ratioMin ≥ (2 : ℝ),
      ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
      ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
      ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
      ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant timingError : ℝ),
      1 ≤ boundaryConstant → 0 ≤ timingError →
      (2 * Real.sqrt 2 + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ (index : Fin count) (nonterminal : index.val + 1 < count),
      ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
      let changed : Scales := {scales with frequency := frequency}
      let motion := prepared.trajectory.movingFamily.patchMotion
      (∀ source : Fin count, index.val < source.val →
        let length := changed.length (source.val + 1)
        0 ≤ entry source ∧ entry source ≤ path.stop ∧ 512 ≤ initialDistance source ∧
        initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
        ‖firstDipoleSeparation motion (entry source) source - (length : ℂ) * direction source‖ ≤ length / 64 ∧
        ‖secondDipoleSeparation motion (entry source) source - (length : ℂ) * (-direction source)‖ ≤ length / 64 ∧
        (3 / 4 : ℝ) * length * initialDistance source ≤
          (Complex.I * star (direction source) * (firstDipoleCenter motion (entry source) source -
            secondDipoleCenter motion (entry source) source)).re ∧
        ‖firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source‖ ≤
          (5 / 4 : ℝ) * length * initialDistance source) →
      (∀ source : Fin count, index.val < source.val → ∀ time ∈ Icc 0 (entry source),
        (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
          quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
            extent * changed.length (source.val + 1)) ∧
        (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
          extent * changed.length (source.val + 1))) →
      ∀ magnitude : Fin count → ℝ,
      let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
        ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
        ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
      (∀ source : Fin count, index.val < source.val → 0 ≤ magnitude source ∧ ∀ time ∈ Icc 0 (entry source),
        sharpState source time ≤ magnitude source * Real.exp (sourceRate * changed.omega (source.val + 1) * (time - entry source))) →
      (∀ source : Fin count, index.val < source.val → magnitude source ≤ magnitudeMax) →
      (∀ source : Fin count, index.val < source.val → initialDistance source ≤ distanceMax) →
      (∀ source : Fin count, index.val < source.val → ∀ time ∈ Icc 0 (entry source), ∀ patch,
        motion.domain time source patch ⊆ Metric.closedBall (quadrupoleCenter motion time source)
          (extent * changed.length (source.val + 1))) →
      ∀ actualTime : ℕ → ℝ, (∀ source : Fin count, actualTime (source.val + 1) = entry source) →
      |actualTime (index.val + 2) - changed.predictedTime sectionTime count (index.val + 2)| ≤
        timingError / changed.omega (index.val + 2) →
      (∀ source : Fin count, index.val < source.val →
        |actualTime (source.val + 1) - changed.predictedTime sectionTime count (source.val + 1)| ≤
          timingError / changed.omega (source.val + 1)) →
      (∀ source : Fin count, index.val < source.val → entry source ≤ entry ⟨index.val + 1, nonterminal⟩) →
      ∀ finish ∈ Icc 0 path.stop,
      (∀ time ∈ Icc 0 finish, |radialShape motion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 finish, |unstableShape motion time index| + |stableShape motion time index| ≤ radius) →
      (∀ receiver : Fin count, receiver.val < index.val → ∀ time ∈ Icc 0 finish,
        |unstableShape motion time receiver| + |stableShape motion time receiver| ≤ radius) →
      (∀ source : Fin count, index.val < source.val →
        2 * (2 * Real.sqrt 2 * changed.omega (index.val + 1)) ≤ sourceRate * changed.omega (source.val + 1)) →
      ∀ suppliedLift : Fin 2 → ℝ → ℝ,
      (∀ side, ContinuousOn (suppliedLift side) (Icc 0 finish)) →
      (∀ side, suppliedLift side 0 = phase (index.val + 1)) →
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (suppliedLift side time : ℂ))) →
      let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
      let shape := fun time =>
        |(referenceStraightenedShape motion graph coordinate index time).1 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
        |(referenceStraightenedShape motion graph coordinate index time).2 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).2|
      let origin := entry ⟨index.val + 1, nonterminal⟩
      changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) ≤ endpointSize →
      ContinuousOn shape (Icc 0 finish) ∧ shape 0 = 0 ∧
      ∀ time ∈ Icc 0 finish,
        shape time < profileMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) ∧
        shape time ≤ (profileMagnitude / 2) * changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) := by
  dsimp only
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth, compatible, rawCap, capPositive, factors⟩ :=
    exists_uniform_actual_domain_shape_profile_improvement
  obtain ⟨chartRadius, chartPositive, _, regularity⟩ :=
    exists_uniform_cascade_paired_chart_regularity graphAnalytic.contDiffAt coordinateSmooth
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth, compatible, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, magnitudeOne,
    rootMin, rootEight, oldRadius, oldPositive, oldQuarter, endpointSize, endpointPositive, factories⟩ :=
    factors factorPositive factorSmall
  let radius := min oldRadius (chartRadius / 2)
  refine ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, magnitudeOne,
    rootMin, rootEight, radius, lt_min oldPositive (by positivity),
    (min_le_left _ _).trans oldQuarter, endpointSize, endpointPositive, ?_⟩
  intro extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  obtain ⟨ratioMin, ratioTwo, factory⟩ :=
    factories extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  refine ⟨ratioMin, ratioTwo, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant referenceNonnegative
    referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError boundaryOne timingErrorNonnegative ratioSeparation
  have ratioBound : 2 ≤ scales.ratio := ratioTwo.trans ratioLarge
  filter_upwards [factory scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError
      boundaryOne timingErrorNonnegative ratioSeparation,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative chartPositive,
    eventually_ge_atTop (1 : ℝ)] with frequency improve referenceSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal entry initialDistance direction entries extents
    magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
    finish finishInside radialSmall targetSmall followerSmall sourceRates suppliedLift suppliedContinuous suppliedInitial suppliedPolar
    endpointBound
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let relative := fun time => referenceStraightenedShape motion graph coordinate index time -
    referenceStraightenedShape prepared.reference graph coordinate index time
  let shape := fun time => |(relative time).1| + |(relative time).2|
  let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  let origin := entry ⟨index.val + 1, nonterminal⟩
  let accuracy := 1 / (64 * (1 + profileConstant))
  let profileMagnitude := 1 + 16 * (leadingMagnitude + accuracy * profileConstant * costMagnitude +
    (accuracy / 3) * additiveMagnitude)
  have targetRegular (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| < chartRadius := by
    fin_cases side
    · have bounded := (targetSmall time inside).trans (min_le_right oldRadius (chartRadius / 2))
      change |unstableShape motion time index| + |stableShape motion time index| < chartRadius
      linarith only [bounded, chartPositive]
    · have actual := referenceSmall prepared.toCascadeMaterialPreparedPair time
        ⟨inside.1, inside.2.trans (finishInside.2.trans path.stopBound)⟩ index
      change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < chartRadius
      have diagonalNonnegative := abs_nonneg (diagonalDifference prepared.reference time index /
        changed.length (index.val + 1) ^ 2 - 1)
      linarith only [actual, diagonalNonnegative]
  have relativeContinuous : ContinuousOn relative (Icc 0 finish) :=
    (regularity prepared.toCascadeMaterialPreparedPair path index finish finishInside.2 targetRegular).1
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) :=
    relativeContinuous.fst.abs.add relativeContinuous.snd.abs
  have relativeInitial : relative 0 = 0 :=
    prepared.toCascadeMaterialPreparedPair.nonterminal_initial_straightened_difference graph coordinate index nonterminal
  have shapeInitial : shape 0 = 0 := by
    dsimp only [shape]
    rw [relativeInitial]
    norm_num
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := zero_lt_two.trans_le ratioBound
  have seedPositive : 0 < changed.seed (index.val + 1) :=
    changed.seed_pos frequencyPositive ratioPositive (index.val + 1)
  have growthPositive : 0 < growth := by
    dsimp only [growth]
    exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))
      (changed.omega_pos frequencyPositive ratioPositive (index.val + 1))
  refine ⟨shapeContinuous, shapeInitial, ?_⟩
  apply General.exponential_profile_of_prefix_half_improvement shapeContinuous shapeInitial
    (zero_lt_one.trans_le magnitudeOne) seedPositive
  intro time timeInside bootstrap
  have subset : Icc 0 time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl timeInside.2
  have targetBound (current : ℝ) (inside : current ∈ Icc 0 time) :
      |unstableShape motion current index| + |stableShape motion current index| ≤ oldRadius :=
    (targetSmall current (subset inside)).trans (min_le_left _ _)
  have followerBound (receiver : Fin count) (below : receiver.val < index.val)
      (current : ℝ) (inside : current ∈ Icc 0 time) :
      |unstableShape motion current receiver| + |stableShape motion current receiver| ≤ oldRadius :=
    (followerSmall receiver below current (subset inside)).trans (min_le_left _ _)
  have endpoint : changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) ≤ endpointSize :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right timeInside.2 origin) growthPositive.le)) seedPositive.le).trans endpointBound
  have improved := improve count phase dipoleAngle prepared path index nonterminal entry initialDistance direction entries extents
    magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
    time ⟨timeInside.1, timeInside.2.trans finishInside.2⟩
    (fun current inside => radialSmall current (subset inside)) targetBound followerBound sourceRates suppliedLift
    (fun side => (suppliedContinuous side).mono subset) suppliedInitial
    (fun side current inside => suppliedPolar side current (subset inside)) bootstrap endpoint
  exact improved.2.2

end EulerNonuniqueness.Paper

