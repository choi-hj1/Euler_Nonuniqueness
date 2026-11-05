import EulerNonuniqueness.Section5.CascadeDomainShapeProfileBootstrap
import EulerNonuniqueness.Section5.CascadeGivenMapSharpProfileEndpoint
import EulerNonuniqueness.Section5.CascadeDomainAllForeignWeightedClosure

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_domain_sharp_profile_bootstrap :
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
      ∃ fullProfileConstant ≥ (1 : ℝ), ∃ sourceMagnitude ≥ (1 : ℝ),
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
      let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
      let shape := fun time =>
        |(referenceStraightenedShape motion graph coordinate index time).1 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
        |(referenceStraightenedShape motion graph coordinate index time).2 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).2|
      let origin := entry ⟨index.val + 1, nonterminal⟩
      changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) ≤ endpointSize →
      ∃ lift : Fin 2 → ℝ → ℝ,
      (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift side time : ℂ))) ∧
      let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
      let state := fun time => prepared.finiteCoordinateSize graph coordinate lift index time + raw time
      let sharp := fun time => prepared.rawSourceCenteredState time index +
        ‖relativeNormalizedFirstMoment changed motion prepared.reference index time‖ +
        ‖quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index‖ / changed.location (index.val + 1) + raw time
      let forcing := fun time => prepared.finiteCoordinateForeignForcing index time + prepared.physicalForeignSourceForcing index time
      ContinuousOn shape (Icc 0 finish) ∧ shape 0 = 0 ∧
      (∀ time ∈ Icc 0 finish,
        shape time < profileMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) ∧
        shape time ≤ (profileMagnitude / 2) * changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) ∧
      ContinuousOn state (Icc 0 finish) ∧ state 0 = 0 ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * state time) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * forcing time) volume 0 finish ∧
      ∀ time ∈ Icc 0 finish,
        state time ≤ fullProfileConstant * (2 * profileMagnitude + sourceMagnitude) *
          changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) ∧
        sharp time ≤ fullProfileConstant * (2 * profileMagnitude + sourceMagnitude) *
          changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) := by
  dsimp only
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, shapeThreshold, shapeThresholdPositive, shapeEighth, compatible, shapeCap, shapeCapPositive, shapeFactors⟩ :=
    exists_uniform_actual_domain_shape_profile_bootstrap
  obtain ⟨sharpThreshold, sharpThresholdPositive, _, sharpCap, sharpCapPositive, sharpFactors⟩ :=
    exists_uniform_actual_given_map_sharp_profile_endpoint graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨allThreshold, allThresholdPositive, _, allCap, allCapPositive,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    sharpIncoming, sharpIncomingNonnegative, sharpOutgoing, sharpOutgoingNonnegative, allFactors⟩ :=
    exists_uniform_actual_given_map_domain_all_foreign_weighted_closure graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  let thresholdMax := min shapeThreshold (min sharpThreshold allThreshold)
  let rawCap := min shapeCap (min sharpCap allCap)
  have shapeCapBound : rawCap ≤ shapeCap := min_le_left _ _
  have sharpCapBound : rawCap ≤ sharpCap := (min_le_right _ _).trans (min_le_left _ _)
  have allCapBound : rawCap ≤ allCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, thresholdMax, lt_min shapeThresholdPositive (lt_min sharpThresholdPositive allThresholdPositive),
    (min_le_left _ _).trans shapeEighth, compatible, rawCap,
    lt_min shapeCapPositive (lt_min sharpCapPositive allCapPositive), ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, magnitudeOne,
    shapeRoot, shapeEight, shapeRadius, shapeRadiusPositive, shapeQuarter, endpointSize, endpointPositive, shapes⟩ :=
    shapeFactors factorPositive factorSmall
  obtain ⟨sharpRadius, sharpRadiusPositive, _, fullProfileConstant, fullProfileOne, sharpRoot, sharpEight, sharpFactory⟩ :=
    sharpFactors factor factorPositive factorSmall
  obtain ⟨allRadius, allRadiusPositive, _, followerConstant, followerOne, allRoot, allEight, alls⟩ :=
    allFactors factor factorPositive factorSmall
  let sourceMagnitude := 1 + 8 * (4 * sharpOutgoing + 1) + 32 * followerConstant * (4 * commonOutgoing + 1)
  have sourceOne : 1 ≤ sourceMagnitude := by
    dsimp only [sourceMagnitude]
    have first : 0 ≤ 8 * (4 * sharpOutgoing + 1) := by positivity
    have second : 0 ≤ 32 * followerConstant * (4 * commonOutgoing + 1) := by positivity
    linarith only [first, second]
  let rootMin := max shapeRoot (max sharpRoot allRoot)
  let radius := min shapeRadius (min sharpRadius allRadius)
  refine ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, magnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, rootMin,
    shapeEight.trans (le_max_left _ _), radius,
    lt_min shapeRadiusPositive (lt_min sharpRadiusPositive allRadiusPositive),
    (min_le_left _ _).trans shapeQuarter, endpointSize, endpointPositive, ?_⟩
  intro extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  obtain ⟨shapeRatio, shapeTwo, shapeFactory⟩ :=
    shapes extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  obtain ⟨allRatio, allMinimum, allFactory⟩ :=
    alls extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  let ratioMin := max shapeRatio allRatio
  refine ⟨ratioMin, shapeTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant referenceNonnegative
    referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError boundaryOne timingErrorNonnegative ratioSeparation
  have ratioBound : 2 ≤ scales.ratio := (shapeTwo.trans (le_max_left _ _)).trans ratioLarge
  filter_upwards [shapeFactory scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity
      ((le_max_left _ _).trans ratioLarge) alphaPositive alphaSmall ratioPower referenceConstant referenceNonnegative
      referenceAmplitude threshold (thresholdBound.trans (min_le_left _ _)) orbit sectionTime boundaryConstant timingError
      boundaryOne timingErrorNonnegative ratioSeparation,
    sharpFactory scales scaleRoot ((le_max_left _ _).trans ((le_max_right _ _).trans rootLarge)) amplitudeIdentity
      ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans ((min_le_right _ _).trans (min_le_left _ _))) referenceNonnegative boundaryOne,
    allFactory scales scaleRoot ((le_max_right _ _).trans ((le_max_right _ _).trans rootLarge)) amplitudeIdentity
      ((le_max_right _ _).trans ratioLarge) alphaPositive alphaSmall ratioPower referenceConstant referenceNonnegative
      referenceAmplitude threshold (thresholdBound.trans ((min_le_right _ _).trans (min_le_right _ _)))
      orbit sectionTime boundaryConstant 1 timingError boundaryOne (by norm_num) timingErrorNonnegative ratioSeparation]
    with frequency shapeEstimate sharpEstimate allEstimate
  intro count phase dipoleAngle inputRadius monitor prepared path index nonterminal entry initialDistance direction entries extents
    magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
    finish finishInside radialSmall targetSmall followerSmall sourceRates endpointBound
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  let shape := fun time =>
    |(referenceStraightenedShape motion graph coordinate index time).1 -
      (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
    |(referenceStraightenedShape motion graph coordinate index time).2 -
      (referenceStraightenedShape prepared.reference graph coordinate index time).2|
  let origin := entry ⟨index.val + 1, nonterminal⟩
  let accuracy := 1 / (64 * (1 + profileConstant))
  let profileMagnitude := 1 + 16 * (leadingMagnitude + accuracy * profileConstant * costMagnitude +
    (accuracy / 3) * additiveMagnitude)
  have rawInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have sizeInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).finiteCoordinateSize = prepared.finiteCoordinateSize := rfl
  have selectedInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).selectedForeignForcing = prepared.selectedForeignForcing := rfl
  have forcingInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).finiteCoordinateForeignForcing = prepared.finiteCoordinateForeignForcing := rfl
  have physicalInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).physicalForeignSourceForcing = prepared.physicalForeignSourceForcing := rfl
  have sharpData := sharpEstimate count phase dipoleAngle (prepared.enlargeCap sharpCapBound) path index nonterminal finish
    finishInside.1 finishInside.2
    (fun time inside => (targetSmall time inside).trans ((min_le_right _ _).trans (min_le_left _ _)))
  dsimp only at sharpData
  simp only [rawInvariant, centeredInvariant, sizeInvariant, forcingInvariant, physicalInvariant] at sharpData
  obtain ⟨lift, liftContinuous, liftPolar, stateContinuous, stateInitial, forcingI, endpoints⟩ := sharpData
  have shapeData := shapeEstimate count phase dipoleAngle (prepared.enlargeCap shapeCapBound) path index nonterminal
    entry initialDistance direction entries extents magnitude
    (by simpa only [rawInvariant, centeredInvariant] using profiles) magnitudeUpper distanceUpper domains actualTime timeIdentity
    nearestTiming sourceTiming timeOrder finish finishInside radialSmall
    (fun time inside => (targetSmall time inside).trans (min_le_left _ _))
    (fun receiver below time inside => (followerSmall receiver below time inside).trans (min_le_left _ _))
    sourceRates lift (fun side => (liftContinuous side).1.continuousOn) (fun side => (liftContinuous side).2)
    liftPolar endpointBound
  dsimp only at shapeData
  obtain ⟨shapeContinuous, shapeInitial, shapeBounds⟩ := shapeData
  have allData := allEstimate count phase dipoleAngle (prepared.enlargeCap allCapBound) path index nonterminal
    entry initialDistance direction entries extents magnitude
    (by simpa only [rawInvariant, centeredInvariant] using profiles) magnitudeUpper distanceUpper domains actualTime timeIdentity
    nearestTiming sourceTiming timeOrder finish finishInside radialSmall
    (fun time inside => (targetSmall time inside).trans ((min_le_right _ _).trans (min_le_right _ _)))
    (fun receiver below time inside => (followerSmall receiver below time inside).trans ((min_le_right _ _).trans (min_le_right _ _)))
    sourceRates
  dsimp only at allData
  simp only [rawInvariant, centeredInvariant, selectedInvariant, forcingInvariant, physicalInvariant] at allData
  obtain ⟨_, shapeI, allI, literalBound, allBound⟩ := allData
  have seedNonnegative : 0 ≤ changed.seed (index.val + 1) := by dsimp only [Scales.seed]; positivity
  have shapeProfile (time : ℝ) (inside : time ∈ Icc 0 finish) :
      shape time ≤ profileMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) :=
    (shapeBounds time inside).1.le
  have shapeAction := intervalIntegral.integral_exp_neg_mul_le_of_same_rate_majorant finishInside.1 shapeI shapeProfile
  have shapeReduced : (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * shape time) ≤
      profileMagnitude * changed.seed (index.val + 1) * Real.exp (-growth * origin) := by
    calc
      _ ≤ finish * (profileMagnitude * changed.seed (index.val + 1)) * Real.exp (-growth * origin) := shapeAction
      _ ≤ 1 * (profileMagnitude * changed.seed (index.val + 1)) * Real.exp (-growth * origin) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (finishInside.2.trans path.stopBound)
          (mul_nonneg (show 0 ≤ profileMagnitude from zero_le_one.trans magnitudeOne) seedNonnegative)) (Real.exp_pos _).le
      _ = _ := by ring
  let forcing := fun time => prepared.finiteCoordinateForeignForcing index time + prepared.physicalForeignSourceForcing index time
  have forcingBound : (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * forcing time) ≤
      ((profileMagnitude + sourceMagnitude) * changed.seed (index.val + 1)) * Real.exp (-growth * origin) := by
    have comparison := intervalIntegral.integral_mono_on finishInside.1 forcingI allI (by
      intro time inside
      exact mul_le_mul_of_nonneg_left (literalBound time inside) (Real.exp_pos _).le)
    calc
      _ ≤ _ := comparison
      _ ≤ (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * shape time) +
          sourceMagnitude * changed.seed (index.val + 1) * Real.exp (-growth * origin) := by
        simpa only [one_mul] using allBound
      _ ≤ profileMagnitude * changed.seed (index.val + 1) * Real.exp (-growth * origin) +
          sourceMagnitude * changed.seed (index.val + 1) * Real.exp (-growth * origin) :=
        add_le_add_right shapeReduced _
      _ = _ := by ring
  have exponential : Continuous (fun time : ℝ => Real.exp (-growth * time)) := by fun_prop
  have stateI := (exponential.continuousOn.mul stateContinuous).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  refine ⟨lift, liftContinuous, liftPolar, shapeContinuous, shapeInitial, shapeBounds,
    stateContinuous, stateInitial, stateI, forcingI, ?_⟩
  intro time inside
  have actual := endpoints origin (profileMagnitude * changed.seed (index.val + 1))
    ((profileMagnitude + sourceMagnitude) * changed.seed (index.val + 1))
    (mul_nonneg (zero_le_one.trans magnitudeOne) seedNonnegative)
    (mul_nonneg (add_nonneg (zero_le_one.trans magnitudeOne) (zero_le_one.trans sourceOne)) seedNonnegative)
    shapeProfile forcingBound time inside
  constructor
  · calc
      _ ≤ fullProfileConstant * (profileMagnitude * changed.seed (index.val + 1) +
          (profileMagnitude + sourceMagnitude) * changed.seed (index.val + 1)) * Real.exp (growth * (time - origin)) := actual.1
      _ = _ := by dsimp only [profileMagnitude, accuracy]; ring
  · calc
      _ ≤ fullProfileConstant * (profileMagnitude * changed.seed (index.val + 1) +
          (profileMagnitude + sourceMagnitude) * changed.seed (index.val + 1)) * Real.exp (growth * (time - origin)) := actual.2
      _ = _ := by dsimp only [profileMagnitude, accuracy]; ring

end EulerNonuniqueness.Paper

