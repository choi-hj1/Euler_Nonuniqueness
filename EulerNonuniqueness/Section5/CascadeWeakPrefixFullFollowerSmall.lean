import EulerNonuniqueness.Section5.CascadeDomainRadialPhysicalBootstrap
import EulerNonuniqueness.Section5.CascadeGivenMapStrongFollowerPrefixResolvedSourceEnvelope
import EulerNonuniqueness.Section5.CascadeFullFollowerDriverSmall
import EulerNonuniqueness.Section1.SwitchedSourceResponseSeedSmall
import EulerNonuniqueness.Section6.SourcePacketBoundedRadiusNeutralSmall

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private def oneBasedExtension {count : ℕ} (values : Fin count → ℝ) (index : ℕ) : ℝ :=
  if h : index - 1 < count then values ⟨index - 1, h⟩ else 0

private theorem oneBasedExtension_apply {count : ℕ} (values : Fin count → ℝ) (index : Fin count) :
    oneBasedExtension values (index.val + 1) = values index := by
  simp only [oneBasedExtension, Nat.add_sub_cancel_right, index.isLt, dite_true]

theorem exists_uniform_actual_weak_prefix_full_follower_small :
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
      ∃ rootMin ≥ (8 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ endpointSize > (0 : ℝ),
      endpointSize ≤ 1 ∧ ∀ precision : ℝ, 0 < precision →
      ∀ extent magnitudeMax distanceMax sourceRate : ℝ,
      1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < sourceRate → sourceRate < 1 / 8 →
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
    coordinateDerivative, chartConstant, chartOne, targetThreshold, targetPositive, targetEighth,
    compatible, targetCap, targetCapPositive, targetFactors⟩ := exists_uniform_actual_domain_radial_physical_bootstrap
  obtain ⟨responseThreshold, responsePositive, _, responseCap, responseCapPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, responseFactors⟩ :=
    exists_uniform_actual_given_map_strong_follower_prefix_resolved_source_envelope
      graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨driverCap, driverCapPositive, driverFactory⟩ := exists_uniform_actual_full_follower_driver_small
  let rawCap := min targetCap (min responseCap driverCap)
  let thresholdMax := min targetThreshold responseThreshold
  have capPositive : 0 < rawCap := lt_min targetCapPositive (lt_min responseCapPositive driverCapPositive)
  have capTarget : rawCap ≤ targetCap := min_le_left _ _
  have capResponse : rawCap ≤ responseCap := (min_le_right _ _).trans (min_le_left _ _)
  have capDriver : rawCap ≤ driverCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, lt_min targetPositive responsePositive,
    (min_le_left _ _).trans targetEighth, compatible, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRoot, targetRootEight,
    targetRadius, targetRadiusPositive, targetRadiusQuarter, targetEndpoint, targetEndpointPositive, targetParameters⟩ :=
    targetFactors factorPositive factorSmall
  obtain ⟨responseRadius, responseRadiusPositive, _, constant, constantOne, comparison, comparisonOne,
    geometry, geometryOne, row, rowNonnegative, responseRatio, responseRatioBound,
    responseRoot, responseRootEight, responseParameters⟩ := responseFactors factor factorPositive factorSmall
  let multiplier := comparison * constant
  let accuracy := 1 / (64 * (1 + profileConstant))
  let profileMagnitude := 1 + 16 * (leadingMagnitude + accuracy * profileConstant * costMagnitude +
    (accuracy / 3) * additiveMagnitude)
  let currentMagnitude := fullProfileConstant * (2 * profileMagnitude + sourceMagnitude)
  have currentNonnegative : 0 ≤ currentMagnitude := by
    have : 1 ≤ profileMagnitude := profileMagnitudeOne
    dsimp only [currentMagnitude]
    positivity
  have multiplierPositive : 0 < multiplier := by dsimp only [multiplier]; positivity
  let rootMin := max targetRoot responseRoot
  let radius := min targetRadius responseRadius
  let endpointSize := min targetEndpoint 1
  refine ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRadius, targetRadiusPositive, targetRadiusQuarter,
    rootMin, targetRootEight.trans (le_max_left _ _), radius,
    lt_min targetRadiusPositive responseRadiusPositive, (min_le_left _ _).trans targetRadiusQuarter,
    endpointSize, lt_min targetEndpointPositive zero_lt_one, min_le_right _ _, ?_⟩
  intro precision precisionPositive extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative
    distanceNonnegative sourceRatePositive sourceRateSmall
  obtain ⟨targetRatio, targetRatioTwo, targetScales⟩ := targetParameters extent magnitudeMax distanceMax sourceRate
    extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  let ratioMin := max targetRatio (max responseRatio (4 * constant))
  refine ⟨ratioMin, targetRatioTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError
    boundaryOne timingNonnegative ratioSeparation
  have targetRatioLarge : targetRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have responseRatioLarge : responseRatio ≤ scales.ratio := (le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge)
  have fourConstant : 4 * constant ≤ scales.ratio := (le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge)
  have ratioBound : 2 ≤ scales.ratio := targetRatioTwo.trans targetRatioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans
    (targetRootEight.trans ((le_max_left _ _).trans rootLarge))
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := (thresholdBound.trans (min_le_left _ _)).trans targetEighth
  have scalarSeparation : (Real.sqrt 2 + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) := by
    have sqrtNonnegative := Real.sqrt_nonneg (2 : ℝ)
    linarith only [ratioSeparation, sqrtNonnegative]
  let feedbackCap := multiplier * (row * geometry + geometry)
  have feedbackCapNonnegative : 0 ≤ feedbackCap := by dsimp only [feedbackCap]; positivity
  have rhoLimit := ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
    ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576)
  simp only [mul_zero, zero_add] at rhoLimit
  filter_upwards [targetScales scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity
      targetRatioLarge alphaPositive alphaSmall ratioPower referenceConstant referenceNonnegative referenceAmplitude threshold
      (thresholdBound.trans (min_le_left _ _)) orbit sectionTime boundaryConstant timingError boundaryOne timingNonnegative ratioSeparation,
    responseParameters extent extentOne 1 zero_lt_one scales scaleRoot ((le_max_right _ _).trans rootLarge)
      amplitudeIdentity responseRatioLarge alphaPositive referenceConstant referenceNonnegative referenceAmplitude threshold
      (thresholdBound.trans (min_le_right _ _)) orbit sectionTime boundaryConstant boundaryOne,
    driverFactory currentMagnitude multiplier row currentNonnegative multiplierPositive.le rowNonnegative
      (precision / 2) (half_pos precisionPositive) scales amplitudePositive ratioBound alphaPositive
      orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne thresholdSmall referenceNonnegative,
    scales.eventually_switched_source_response_seed_small ratioBound alphaPositive alphaSmall ratioPower
      sourceRatePositive sourceRateSmall timingNonnegative scalarSeparation sectionTime incomingNonnegative outgoingNonnegative
      (zero_le_one.trans extentOne) magnitudeNonnegative distanceNonnegative (by norm_num : (0 : ℝ) ≤ 1)
      (show 0 < precision / (2 * multiplier) by positivity),
    scales.eventually_bounded_radius_source_neutral_small amplitudePositive ratioBound alphaPositive
      (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne) (zero_lt_one.trans_le extentOne) zero_lt_one,
    rhoLimit.eventually (eventually_lt_nhds zero_lt_one),
    eventually_ge_atTop (4 * feedbackCap + 1)]
      with frequency targetEstimate responseEstimate driverEstimate scalarEstimate neutral rhoSmall frequencyLarge
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal entry initialDistance direction
  dsimp only
  intro entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming
    sourceTiming timeOrder finish finishInside followerSmall sourceRates endpointBound
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let growth := 2 * Real.sqrt 2 * omega
  let origin := entry ⟨index.val + 1, nonterminal⟩
  let seed := changed.seed (index.val + 1)
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let rate := constant * omega / changed.ratio + multiplier * (row * geometry * rho + 1 * geometry)
  let finer := Finset.univ.filter (fun source : Fin count => index.val < source.val)
  let sourceEnvelope := fun time => ∑ source ∈ finer,
    if time ≤ entry source then incomingConstant * extent ^ 2 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
      (1 + (changed.location (source.val + 1))⁻¹) * magnitude source * Real.exp (sourceRate * changed.omega (source.val + 1) * (time - entry source))
    else outgoingConstant * changed.circulation (source.val + 1) * (changed.circulation (source.val + 1) * (time - entry source) +
      (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 + ‖centroidAsymmetry motion (entry source) source‖)
  have frequencyPositive : 0 < frequency := by linarith only [frequencyLarge, feedbackCapNonnegative]
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaLower : frequency ≤ omega := changed.omega_ge_frequency frequencyPositive
    (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _
  have growthPositive : 0 < growth := by dsimp only [growth]; positivity
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  have rhoNonnegative : 0 ≤ rho := by
    have hessian : 0 ≤ changed.hessian := tsum_nonneg fun source => div_nonneg
      (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le 3)
    have strain : 0 ≤ changed.strain := tsum_nonneg fun source => div_nonneg
      (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    dsimp only [rho]; positivity
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have rateBound : rate ≤ growth / 4 := by
    have coarse : constant * omega / changed.ratio ≤ omega / 4 := by
      apply (div_le_iff₀ ratioPositive).mpr
      change constant * omega ≤ omega / 4 * scales.ratio
      nlinarith only [mul_le_mul_of_nonneg_left fourConstant omegaPositive.le]
    have feedback : multiplier * (row * geometry * rho + 1 * geometry) ≤ feedbackCap := by
      have scaled := mul_le_mul_of_nonneg_left rhoSmall.le (show 0 ≤ row * geometry by positivity)
      change row * geometry * rho ≤ row * geometry * 1 at scaled
      dsimp only [feedbackCap]
      nlinarith only [mul_le_mul_of_nonneg_left scaled multiplierPositive.le]
    have cap : feedbackCap ≤ omega / 4 := by linarith only [frequencyLarge, omegaLower]
    have halfBound : rate ≤ omega / 2 := by
      calc
        _ ≤ omega / 4 + feedbackCap := add_le_add coarse feedback
        _ ≤ omega / 4 + omega / 4 := add_le_add_left cap _
        _ = omega / 2 := by ring
    have sqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    have growthBound : omega / 2 ≤ growth / 4 := by
      dsimp only [growth]
      nlinarith only [mul_le_mul_of_nonneg_right sqrtOne omegaPositive.le]
    exact halfBound.trans growthBound
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  have macroInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have driverInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).weightedMacroSourceState = prepared.weightedMacroSourceState := by
    funext time source
    simp only [CascadeSourcePreparedPair.weightedMacroSourceState, macroInvariant]
  have target := targetEstimate count phase dipoleAngle (prepared.enlargeCap capTarget) path index nonterminal
    entry initialDistance direction entries extents magnitude (by simpa only [rawInvariant, centeredInvariant] using sourceProfiles)
    magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder finish finishInside
    (fun receiver below time inside => (followerSmall receiver below time inside).trans (min_le_left _ _)) sourceRates
    (endpointBound.trans (min_le_left _ _))
  dsimp only at target
  simp only [rawInvariant, centeredInvariant] at target
  have targetData := target
  obtain ⟨_, _, targetLift, _, _, _, _, _, _, _, _, _, targetBounds⟩ := target
  have currentProfile (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.rawSourceCenteredState time index +
        ‖relativeNormalizedFirstMoment changed motion prepared.reference index time‖ +
        ‖quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index‖ / changed.location (index.val + 1) +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
          currentMagnitude * seed * Real.exp (growth * (time - origin)) := (targetBounds time inside).2
  obtain ⟨lift, liftProperties, liftPolar, responseData⟩ := responseEstimate count phase dipoleAngle
    (prepared.enlargeCap capResponse) path index nonterminal finish finishInside.1 finishInside.2 entry initialDistance direction
    entries extents sourceRate sourceRatePositive magnitude (by simpa only [rawInvariant, centeredInvariant] using sourceProfiles)
    (fun receiver below time inside => (followerSmall receiver below time inside).trans (min_le_right _ _))
  dsimp only at responseData
  simp only [rawInvariant, driverInvariant] at responseData
  obtain ⟨_, _, _, _, _, _, _, _, _, sourceI, history⟩ := responseData
  let envelope := fun time => ‖fun receiver : Fin count => if receiver.val < index.val then
    changed.location (receiver.val + 1) ^ 4 * (prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch) else 0‖
  have exposureAt (time : ℝ) (inside : time ∈ Icc 0 finish) : seed * Real.exp (growth * (time - origin)) ≤ endpointSize :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 origin) growthPositive.le)) seedPositive.le).trans endpointBound
  have neutralBound (source : Fin count) (below : index.val < source.val) :
      ‖centroidAsymmetry motion (entry source) source‖ ≤ changed.length (source.val + 1) ^ 2 := by
    have actual := neutral prepared.toCascadeMaterialPreparedPair path
      (thresholdSmall.trans (by norm_num)) (factorSmall.trans (by norm_num)) source (entry source)
      (entries source below).1 (entries source below).2.1 (domains source below)
      (entry source) ⟨(entries source below).1, le_rfl⟩
    simpa only [one_mul] using actual
  let paper : Fin count → ℕ := fun source => source.val + 1
  have paperInjective : Function.Injective paper := by intro first second equal; apply Fin.ext; dsimp only [paper] at equal; omega
  let selected := finer.image paper
  let natMagnitude := oneBasedExtension magnitude
  let natDistance := oneBasedExtension initialDistance
  let natNeutral := oneBasedExtension (fun source => ‖centroidAsymmetry motion (entry source) source‖)
  have originIdentity : actualTime (index.val + 2) = origin := by
    simpa only [origin] using timeIdentity ⟨index.val + 1, nonterminal⟩
  have natSourceEquality (time : ℝ) :
      (∑ source ∈ selected,
        if time ≤ actualTime source then incomingConstant * extent ^ 2 * changed.circulation source * changed.length source ^ 2 *
          (1 + (changed.location source)⁻¹) * natMagnitude source * Real.exp (sourceRate * changed.omega source * (time - actualTime source))
        else outgoingConstant * changed.circulation source * (changed.circulation source * (time - actualTime source) +
          (1 + natDistance source) * changed.length source ^ 2 + natNeutral source)) = sourceEnvelope time := by
    rw [Finset.sum_image (fun first _ second _ equal => paperInjective equal)]
    apply Finset.sum_congr rfl
    intro source _
    simp only [paper, timeIdentity, natMagnitude, natDistance, natNeutral, oneBasedExtension_apply]
  refine ⟨targetData, lift, liftProperties, liftPolar, ?_⟩
  intro time inside receiver below
  have scalar := scalarEstimate count (index.val + 1) selected (by
      intro source member
      obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
      have finerSource := (Finset.mem_filter.mp sourceMember).2
      dsimp only [paper]; omega) actualTime
    (by rw [originIdentity]; exact (entries ⟨index.val + 1, nonterminal⟩ (by simp)).1)
    nearestTiming (by
      intro source member
      obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
      exact sourceTiming source (Finset.mem_filter.mp sourceMember).2)
    (by
      intro source member
      obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
      have finerSource := (Finset.mem_filter.mp sourceMember).2
      dsimp only [paper]
      rw [timeIdentity, originIdentity]
      exact ⟨(entries source finerSource).1, timeOrder source finerSource⟩)
    (by
      intro source member
      obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
      have actual := sourceRates source (Finset.mem_filter.mp sourceMember).2
      have sqrtNonnegative := Real.sqrt_nonneg (2 : ℝ)
      have scaled := mul_nonneg sqrtNonnegative omegaPositive.le
      change Real.sqrt 2 * omega ≤ sourceRate * changed.omega (source.val + 1)
      linarith only [actual, scaled]) natMagnitude natDistance natNeutral
    (by
      intro source member
      obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
      have finerSource := (Finset.mem_filter.mp sourceMember).2
      simpa only [paper, natMagnitude, oneBasedExtension_apply] using
        ⟨(sourceProfiles source finerSource).1, magnitudeUpper source finerSource⟩)
    (by
      intro source member
      obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
      have finerSource := (Finset.mem_filter.mp sourceMember).2
      have nonnegative : 0 ≤ initialDistance source := by linarith only [(entries source finerSource).2.2.1]
      simpa only [paper, natDistance, oneBasedExtension_apply] using ⟨nonnegative, distanceUpper source finerSource⟩)
    (by
      intro source member
      obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
      have finerSource := (Finset.mem_filter.mp sourceMember).2
      simpa only [paper, natNeutral, oneBasedExtension_apply, one_mul] using
        ⟨norm_nonneg (centroidAsymmetry motion (entry source) source), neutralBound source finerSource⟩)
    rate time endpointSize rateNonnegative (by
      change rate ≤ Real.sqrt 2 * omega / 2
      change rate ≤ growth / 4 at rateBound
      dsimp only [growth] at rateBound
      linarith only [rateBound])
    inside.1 (min_le_right _ _) (by simpa only [originIdentity] using exposureAt time inside)
  dsimp only at scalar
  have sourceKernelI : IntervalIntegrable (fun current => Real.exp (rate * (time - current)) * sourceEnvelope current)
      volume 0 time := by
    convert scalar.2.1 using 1
    funext current
    exact congrArg (fun value : ℝ => Real.exp (rate * (time - current)) * value) (natSourceEquality current).symm
  have sourceSmall : (∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * sourceEnvelope current) / changed.location (index.val + 1) ^ 4 ≤
        precision / (2 * multiplier) := by
    convert scalar.2.2 using 1
    congr 1
    apply intervalIntegral.integral_congr
    intro current _
    exact congrArg (fun value : ℝ => Real.exp (rate * (time - current)) * value) (natSourceEquality current).symm
  have driver := driverEstimate count phase dipoleAngle (prepared.enlargeCap capDriver) path index time inside.1
    (inside.2.trans finishInside.2) origin rate rateNonnegative rateBound
    (by intro current member; simpa only [rawInvariant, centeredInvariant] using currentProfile current ⟨member.1, member.2.trans inside.2⟩)
    ((exposureAt time inside).trans (min_le_right _ _))
  dsimp only at driver
  simp only [driverInvariant] at driver
  have driverKernelI := driver.2.1
  have driverSmall := driver.2.2.2
  have integralSplit : (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) *
      (row * rho * prepared.weightedMacroSourceState current index + sourceEnvelope current)) =
      (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * row * rho * prepared.weightedMacroSourceState current index) +
      (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * sourceEnvelope current) := by
    simp_rw [mul_add]
    rw [intervalIntegral.integral_add (by simpa only [mul_assoc] using driverKernelI) sourceKernelI]
    congr 1
    apply intervalIntegral.integral_congr
    intro current _
    ring
  have normalized : envelope time / changed.location (index.val + 1) ^ 4 ≤ precision := by
    have actual := (history time inside).2
    change envelope time ≤ multiplier * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) *
      (row * rho * prepared.weightedMacroSourceState current index + sourceEnvelope current) at actual
    rw [integralSplit] at actual
    have divided := div_le_div_of_nonneg_right actual (pow_nonneg (changed.location_pos (index.val + 1)).le 4)
    have sourceScaled := mul_le_mul_of_nonneg_left sourceSmall multiplierPositive.le
    have sourceHalf : multiplier * ((∫ current in (0 : ℝ)..time,
        Real.exp (rate * (time - current)) * sourceEnvelope current) / changed.location (index.val + 1) ^ 4) ≤ precision / 2 := by
      convert sourceScaled using 1
      field_simp
      ring
    have combined := add_le_add driverSmall sourceHalf
    apply divided.trans
    convert combined using 1 <;> ring
  have fullNonnegative : 0 ≤ prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch := by
    have := changed.location_pos (receiver.val + 1)
    have := changed.length_pos (receiver.val + 1)
    dsimp only [CascadeSourcePreparedPair.finiteCoordinateSize, CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have component := norm_le_pi_norm (fun current : Fin count => if current.val < index.val then
    changed.location (current.val + 1) ^ 4 * (prepared.finiteCoordinateSize graph coordinate (lift current) current time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time current patch) else 0) receiver
  have scaledNonnegative := mul_nonneg (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4) fullNonnegative
  simp only [below, ite_true, Real.norm_eq_abs, abs_of_nonneg scaledNonnegative] at component
  have locationOrder : changed.location (index.val + 1) ≤ changed.location (receiver.val + 1) := by
    rw [changed.location_eq_inv_pow, changed.location_eq_inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))
  have scaledOrder := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (changed.location_pos _).le locationOrder 4) fullNonnegative
  have bound := scaledOrder.trans component
  have divided : prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch ≤
        envelope time / changed.location (index.val + 1) ^ 4 :=
    (le_div_iff₀ (pow_pos (changed.location_pos (index.val + 1)) 4)).mpr (by
      calc
        _ = changed.location (index.val + 1) ^ 4 *
            (prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
              ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch) := mul_comm _ _
        _ ≤ envelope time := bound)
  exact divided.trans normalized

end EulerNonuniqueness.Paper
