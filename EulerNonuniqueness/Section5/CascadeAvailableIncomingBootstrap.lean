import EulerNonuniqueness.Section5.CascadeJointIncomingBootstrap
import EulerNonuniqueness.Section5.CascadeIncomingHorizonAvailability
import EulerNonuniqueness.Section1.SeedExposureHorizonAtElapsed

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_available_incoming_bootstrap :
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
      ∃ targetRadius > (0 : ℝ), targetRadius ≤ 1 / 4 ∧
      ∃ rootMin ≥ (8 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ endpointMax > (0 : ℝ),
      endpointMax ≤ 1 ∧ ∀ endpoint : ℝ, 0 < endpoint → endpoint ≤ endpointMax →
      ∀ precision : ℝ, 0 < precision →
      ∀ extent magnitudeMax distanceMax sourceRate : ℝ,
      1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < sourceRate → sourceRate < 1 / 8 →
      ∃ ratioMin ≥ (2 : ℝ),
      ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
      ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
      ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
      ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant timingError : ℝ),
      1 ≤ boundaryConstant → 0 ≤ timingError → 0 < sectionTime →
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
      entry ⟨index.val + 1, nonterminal⟩ ≤ 1 / 2 →
      (∀ source : Fin count, index.val < source.val →
        2 * (2 * Real.sqrt 2 * changed.omega (index.val + 1)) ≤ sourceRate * changed.omega (source.val + 1)) →
      let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
      let origin := entry ⟨index.val + 1, nonterminal⟩
      let finish := origin + Real.log (endpoint / changed.seed (index.val + 1)) / growth
      let shape := fun time =>
        |(referenceStraightenedShape motion graph coordinate index time).1 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
        |(referenceStraightenedShape motion graph coordinate index time).2 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).2|
      0 < finish ∧ 0 < finish - origin ∧ finish - origin < 1 / 4 ∧
      512 ≤ growth * (finish - origin) ∧
      changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) = endpoint ∧
      finish < 3 / 4 ∧ finish ≤ path.stop ∧
      (∀ time ∈ Icc 0 finish, ∀ receiver : Fin count, receiver.val < index.val →
        (|unstableShape motion time receiver| + |stableShape motion time receiver| < radius / 2) ∧
        |radialShape motion time receiver| < 1 / 8) ∧
      ((∀ time ∈ Icc 0 finish, |radialShape motion time index| < 1 / 2) ∧
      (∀ time ∈ Icc 0 finish, |unstableShape motion time index| + |stableShape motion time index| < targetRadius / 2) ∧
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
          changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) ∧
      ∃ lift : Fin count → Fin 2 → ℝ → ℝ,
        (∀ receiver side, Continuous (lift receiver side) ∧ lift receiver side 0 = phase (receiver.val + 1)) ∧
        (∀ receiver : Fin count, receiver.val < index.val → ∀ side, ∀ time ∈ Icc 0 finish,
          positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
            (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
              Complex.exp (Complex.I * (lift receiver side time : ℂ))) ∧
        ∀ time ∈ Icc 0 finish, ∀ receiver : Fin count, receiver.val < index.val →
          prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
            ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch ≤ precision := by
  classical
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    compatible, rawCap, capPositive, factors⟩ := exists_uniform_actual_joint_incoming_bootstrap
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    compatible, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRadius, targetRadiusPositive,
    targetRadiusQuarter, rootMin, rootEight, radius, radiusPositive, radiusQuarter,
    endpointMax, endpointMaxPositive, endpointMaxOne, parameters⟩ := factors factorPositive factorSmall
  refine ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRadius, targetRadiusPositive,
    targetRadiusQuarter, rootMin, rootEight, radius, radiusPositive, radiusQuarter,
    endpointMax, endpointMaxPositive, endpointMaxOne, ?_⟩
  intro endpoint endpointPositive endpointBound precision precisionPositive extent magnitudeMax distanceMax sourceRate
    extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive sourceRateSmall
  obtain ⟨ratioMin, ratioTwo, scalesFactory⟩ := parameters precision precisionPositive extent magnitudeMax distanceMax sourceRate
    extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive sourceRateSmall
  refine ⟨ratioMin, ratioTwo, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError
    boundaryOne timingNonnegative sectionPositive ratioSeparation
  have ratioBound : 2 ≤ scales.ratio := ratioTwo.trans ratioLarge
  have rootPositive : 0 < scaleRoot := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 2 := (thresholdBound.trans thresholdEighth).trans (by norm_num)
  have endpointOne : endpoint ≤ 1 := endpointBound.trans endpointMaxOne
  filter_upwards [scalesFactory scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError
      boundaryOne timingNonnegative ratioSeparation,
    scales.eventually_seed_exposure_horizon_at_elapsed ratioBound alphaPositive alphaSmall sectionPositive endpointPositive
      endpointOne 512 (by norm_num),
    scales.eventually_actual_incoming_horizon_available amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive (factorSmall.trans (by norm_num)) rootPositive (zero_le_one.trans boundaryOne),
    eventually_gt_atTop (0 : ℝ)] with frequency incoming horizonEstimate available frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal entry initialDistance direction
  dsimp only
  intro entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming
    sourceTiming timeOrder originBound sourceRates
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  let seed := changed.seed (index.val + 1)
  let origin := entry ⟨index.val + 1, nonterminal⟩
  let elapsed := Real.log (endpoint / seed) / growth
  let finish := origin + elapsed
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have growthPositive : 0 < growth := by
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
    dsimp only [growth]; positivity
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  have originNonnegative : 0 ≤ origin := (entries ⟨index.val + 1, nonterminal⟩ (by simp)).1
  have clock := horizonEstimate (index.val + 1) (by omega)
  change 0 < elapsed ∧ elapsed < 1 / 4 ∧ 512 ≤ growth * elapsed ∧ seed * Real.exp (growth * elapsed) = endpoint ∧
    ∀ time : ℝ, 0 ≤ time → time ≤ elapsed → seed * Real.exp (growth * time) ≤ endpoint at clock
  have finishPositive : 0 < finish := by dsimp only [finish]; linarith only [originNonnegative, clock.1]
  have finishSmall : finish < 3 / 4 := by dsimp only [finish]; linarith only [originBound, clock.2.1]
  have elapsedIdentity : finish - origin = elapsed := by dsimp only [finish]; ring
  have exposureAt (time : ℝ) (before : time ≤ finish) : seed * Real.exp (growth * (time - origin)) ≤ endpoint := by
    rw [← clock.2.2.2.1]
    apply mul_le_mul_of_nonneg_left _ seedPositive.le
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ growthPositive.le
    dsimp only [finish] at before
    linarith only [before]
  have incomingAt (time : ℝ) (inside : time ∈ Icc 0 path.stop) (before : time ≤ finish) :=
    incoming count phase dipoleAngle prepared path index nonterminal entry initialDistance direction entries extents magnitude
      sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder time inside
      sourceRates ((exposureAt time before).trans endpointBound)
  have radialPrefix (current : Fin count) (below : current.val ≤ index.val) (time : ℝ)
      (inside : time ∈ Icc 0 path.stop) (before : time ≤ finish) : |radialShape motion time current| ≤ 1 / 2 := by
    have payload := incomingAt time inside before
    rcases lt_or_eq_of_le below with earlier | equal
    · exact ((payload.1 time ⟨inside.1, le_rfl⟩ current earlier).2.le).trans (by norm_num)
    · have same : current = index := Fin.ext equal
      subst current
      exact (payload.2.1.1 time ⟨inside.1, le_rfl⟩).le
  have finishAvailable : finish ≤ path.stop := available count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path
    thresholdSmall index nonterminal entry initialDistance direction entries finish (finishSmall.trans (by norm_num)) radialPrefix
  have payload := incomingAt finish ⟨finishPositive.le, finishAvailable⟩ le_rfl
  have elapsedPositive : 0 < finish - origin := by rw [elapsedIdentity]; exact clock.1
  have elapsedSmall : finish - origin < 1 / 4 := by rw [elapsedIdentity]; exact clock.2.1
  have elapsedLarge : 512 ≤ growth * (finish - origin) := by rw [elapsedIdentity]; exact clock.2.2.1
  have exactExposure : seed * Real.exp (growth * (finish - origin)) = endpoint := by
    rw [elapsedIdentity]
    exact clock.2.2.2.1
  exact ⟨finishPositive, elapsedPositive, elapsedSmall, elapsedLarge, exactExposure, finishSmall, finishAvailable, payload⟩

end EulerNonuniqueness.Paper
