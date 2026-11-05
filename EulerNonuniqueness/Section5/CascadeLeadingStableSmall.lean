import EulerNonuniqueness.Section5.CascadeCoarserSourceInputSmall
import EulerNonuniqueness.Section5.CascadeTimedOlderSourceInputSmall
import EulerNonuniqueness.Section5.CascadeAdjacentSourceStableSmall
import EulerNonuniqueness.Section5.CascadeLeadingThreeWaySplit
import EulerNonuniqueness.General.TwoRateExponentialResponse

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_leading_stable_small :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ rootMin ≥ (8 : ℝ),
    ∀ currentMagnitude : ℝ, 0 ≤ currentMagnitude → ∀ tolerance : ℝ, 0 < tolerance →
    ∀ extent magnitudeMax distanceMax sourceRate : ℝ,
    1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < sourceRate →
    ∃ ratioMin ≥ (2 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    4 * Real.sqrt 2 ≤ sourceRate * scales.ratio ^ 2 →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant timingError : ℝ),
    1 ≤ boundaryConstant → 0 ≤ timingError →
    (2 * Real.sqrt 2 + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ (receiver : Fin count) (nonterminal : receiver.val + 1 < count),
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, receiver.val < source.val →
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
    (∀ source : Fin count, receiver.val < source.val → ∀ time ∈ Icc 0 (entry source),
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
    (∀ source : Fin count, receiver.val < source.val → 0 ≤ magnitude source ∧ ∀ time ∈ Icc 0 (entry source),
      sharpState source time ≤ magnitude source * Real.exp (sourceRate * changed.omega (source.val + 1) * (time - entry source))) →
    (∀ source : Fin count, receiver.val < source.val → magnitude source ≤ magnitudeMax) →
    (∀ source : Fin count, receiver.val < source.val → initialDistance source ≤ distanceMax) →
    (∀ source : Fin count, receiver.val < source.val → ∀ time ∈ Icc 0 (entry source), ∀ patch,
      motion.domain time source patch ⊆ Metric.closedBall (quadrupoleCenter motion time source)
        (extent * changed.length (source.val + 1))) →
    ∀ actualTime : ℕ → ℝ, (∀ source : Fin count, actualTime (source.val + 1) = entry source) →
    |actualTime (receiver.val + 2) - changed.predictedTime sectionTime count (receiver.val + 2)| ≤
      timingError / changed.omega (receiver.val + 2) →
    (∀ source : Fin count, receiver.val < source.val →
      |actualTime (source.val + 1) - changed.predictedTime sectionTime count (source.val + 1)| ≤
        timingError / changed.omega (source.val + 1)) →
    (∀ source : Fin count, receiver.val < source.val → entry source ≤ entry ⟨receiver.val + 1, nonterminal⟩) →
    ∀ finish ∈ Icc 0 path.stop,
    (∀ current : Fin count, current.val < receiver.val → ∀ time ∈ Icc 0 finish,
      |unstableShape motion time current| + |stableShape motion time current| ≤ radius) →
    let lambda := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let origin := entry ⟨receiver.val + 1, nonterminal⟩
    (∀ source : Fin count, receiver.val < source.val → 2 * lambda ≤ sourceRate * changed.omega (source.val + 1)) →
    (∀ time ∈ Icc 0 finish, sharpState receiver time ≤ currentMagnitude * changed.seed (receiver.val + 1) *
      Real.exp (lambda * (time - origin))) →
    origin ≤ finish →
    changed.seed (receiver.val + 1) * Real.exp (lambda * (finish - origin)) ≤ 1 →
    let leading := fun time => quadrupoleRelativeLeadingStrain changed motion prepared.reference time receiver
    ContinuousOn leading (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-(lambda / 2) * (finish - time)) * |(leading time).2|) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-(lambda / 2) * (finish - time)) * |(leading time).2|) ≤ tolerance := by
  classical
  obtain ⟨coarseThreshold, coarseThresholdPositive, coarseEighth, coarseCap, coarseCapPositive, coarses⟩ :=
    exists_uniform_actual_coarser_source_input_small
  obtain ⟨olderThreshold, olderThresholdPositive, olderEighth, olderCap, olderCapPositive, olders⟩ :=
    exists_uniform_actual_timed_older_source_input_small
  obtain ⟨nearestThreshold, nearestThresholdPositive, nearestEighth, nearestCap, nearestCapPositive, nearests⟩ :=
    exists_uniform_actual_adjacent_source_stable_small
  let thresholdMax := min coarseThreshold (min olderThreshold nearestThreshold)
  let rawCap := min coarseCap (min olderCap nearestCap)
  have coarseCapBound : rawCap ≤ coarseCap := min_le_left _ _
  have olderCapBound : rawCap ≤ olderCap := (min_le_right _ _).trans (min_le_left _ _)
  have nearestCapBound : rawCap ≤ nearestCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨thresholdMax, lt_min coarseThresholdPositive (lt_min olderThresholdPositive nearestThresholdPositive),
    (min_le_left _ _).trans coarseEighth, rawCap,
    lt_min coarseCapPositive (lt_min olderCapPositive nearestCapPositive), ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, rootMin, rootEight, coarseParameters⟩ := coarses factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, rootMin, rootEight, ?_⟩
  intro currentMagnitude currentNonnegative tolerance tolerancePositive extent magnitudeMax distanceMax sourceRate
    extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  have thirdPositive : 0 < tolerance / 3 := by positivity
  obtain ⟨ratioMin, ratioTwo, coarseFactory⟩ := coarseParameters currentMagnitude currentNonnegative
    (tolerance / 3) thirdPositive extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative
    distanceNonnegative sourceRatePositive
  refine ⟨ratioMin, ratioTwo, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower globalGap referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError
    boundaryOne timingNonnegative ratioSeparation
  have ratioBound : 2 ≤ scales.ratio := ratioTwo.trans ratioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdCoarse : threshold ≤ coarseThreshold := thresholdBound.trans (min_le_left _ _)
  have thresholdOlder : threshold ≤ olderThreshold := thresholdBound.trans ((min_le_right _ _).trans (min_le_left _ _))
  have thresholdNearest : threshold ≤ nearestThreshold := thresholdBound.trans ((min_le_right _ _).trans (min_le_right _ _))
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [coarseFactory scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdCoarse orbit sectionTime boundaryConstant timingError
      boundaryOne timingNonnegative ratioSeparation,
    olders currentMagnitude currentNonnegative (tolerance / 3) thirdPositive extent extentOne sourceRate sourceRatePositive
      magnitudeMax distanceMax magnitudeNonnegative distanceNonnegative scales amplitudePositive ratioBound alphaPositive alphaSmall
      ratioPower globalGap timingError timingNonnegative ratioSeparation referenceConstant referenceNonnegative referenceAmplitude
      threshold thresholdOlder orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    nearests extent extentOne sourceRate sourceRatePositive magnitudeMax distanceMax currentMagnitude magnitudeNonnegative
      distanceNonnegative currentNonnegative (tolerance / 3) thirdPositive scales amplitudePositive ratioBound alphaPositive
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdNearest orbit sectionTime factor scaleRoot
      boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_cascade_leading_three_way_split amplitudePositive ratioBound alphaPositive orbit sectionTime
      (thresholdCoarse.trans coarseEighth) referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_gt_atTop (0 : ℝ)] with frequency coarseEstimate olderEstimate nearestEstimate split frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal entry initialDistance direction
  dsimp only
  intro entries extents magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
    finish finishInside small rateBounds currentProfile entryBefore exposure
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let nearest : Fin count := ⟨receiver.val + 1, nonterminal⟩
  let lambda := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
  let origin := entry nearest
  let sharp := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
    ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
    ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let input := fun source => relativeBlockSourceShapeInput changed motion prepared.reference receiver source
  let leading := fun time => quadrupoleRelativeLeadingStrain changed motion prepared.reference time receiver
  let coarser := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val), input source time
  let older := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => nearest.val < source.val), input source time
  have rawInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centerInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have coarseProfiles := profiles
  have coarseCurrent := currentProfile
  rw [← rawInvariant coarseCapBound, ← centerInvariant coarseCapBound] at coarseProfiles coarseCurrent
  obtain ⟨coarseContinuous, _, coarseI, coarseBound⟩ :=
    coarseEstimate count phase dipoleAngle (prepared.enlargeCap coarseCapBound) path receiver nonterminal
      entry initialDistance direction entries extents magnitude coarseProfiles magnitudeUpper distanceUpper domains actualTime
      timeIdentity nearestTiming sourceTiming timeOrder finish finishInside small rateBounds coarseCurrent
  have olderProfiles : ∀ source : Fin count, receiver.val + 1 < source.val → ∀ time ∈ Icc 0 (entry source),
      sharp source time ≤ magnitude source * Real.exp (sourceRate * changed.omega (source.val + 1) * (time - entry source)) :=
    fun source above => (profiles source (by omega)).2
  have olderCurrent := currentProfile
  change ∀ time ∈ Icc 0 finish, sharp receiver time ≤ currentMagnitude * changed.seed (receiver.val + 1) *
    Real.exp (lambda * (time - origin)) at olderCurrent
  dsimp only [sharp] at olderProfiles olderCurrent
  rw [← rawInvariant olderCapBound, ← centerInvariant olderCapBound] at olderProfiles olderCurrent
  have olderData := olderEstimate count phase dipoleAngle (prepared.enlargeCap olderCapBound) path receiver nonterminal
    entry initialDistance magnitude direction actualTime timeIdentity
    ⟨(entries nearest (by dsimp only [nearest]; omega)).1, (entries nearest (by dsimp only [nearest]; omega)).2.1⟩
    nearestTiming (fun source above => sourceTiming source (by omega))
    (fun source above => by
      rcases entries source (by omega) with ⟨nonnegative, _, rest⟩
      exact ⟨nonnegative, timeOrder source (by omega), rest⟩)
    (fun source above => extents source (by omega)) (fun source above => domains source (by omega))
    (fun source above => ⟨(profiles source (by omega)).1, magnitudeUpper source (by omega)⟩)
    (fun source above => distanceUpper source (by omega)) olderProfiles finish finishInside olderCurrent
  obtain ⟨_, _, olderContinuous, _, _, _, olderI, _, olderBound⟩ := olderData
  have nearestAbove : receiver.val < nearest.val := by dsimp only [nearest]; omega
  rcases entries nearest nearestAbove with ⟨entryNonnegative, _, initialLarge, initialSmall, unit, firstInitial,
    secondInitial, initialProjection, initialUpper⟩
  have driverProfile : ∀ time ∈ Icc 0 (entry nearest), sharp nearest time ≤ magnitudeMax *
      Real.exp (sourceRate * changed.omega (nearest.val + 1) * (time - entry nearest)) := by
    intro time inside
    exact ((profiles nearest nearestAbove).2 time inside).trans
      (mul_le_mul_of_nonneg_right (magnitudeUpper nearest nearestAbove) (Real.exp_pos _).le)
  have nearestCurrent := currentProfile
  dsimp only [sharp] at driverProfile
  rw [← rawInvariant nearestCapBound, ← centerInvariant nearestCapBound] at driverProfile nearestCurrent
  obtain ⟨nearestContinuous, nearestI, _, nearestBound, _⟩ :=
    nearestEstimate count phase dipoleAngle (prepared.enlargeCap nearestCapBound) path receiver nearest rfl
      (entry nearest) finish (initialDistance nearest) entryNonnegative entryBefore finishInside.2 initialLarge
      (distanceUpper nearest nearestAbove) initialSmall (direction nearest) unit firstInitial secondInitial initialProjection initialUpper
      (extents nearest nearestAbove) (domains nearest nearestAbove) driverProfile nearestCurrent exposure
  obtain ⟨leadingContinuous, _, _, _, identity⟩ := split count phase dipoleAngle prepared.toCascadeMaterialPreparedPair
    path receiver nearest rfl
  have leadingOn : ContinuousOn leading (Icc 0 finish) := leadingContinuous.mono (Icc_subset_Icc le_rfl finishInside.2)
  have omegaPositive : 0 < changed.omega (receiver.val + 1) := changed.omega_pos frequencyPositive (by linarith only [ratioBound]) _
  have lambdaPositive : 0 < lambda := by dsimp only [lambda]; positivity
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishInside.2
  have kernel : Continuous (fun time : ℝ => Real.exp (-(lambda / 2) * (finish - time))) := by fun_prop
  have kernelI (function : ℝ → ℝ × ℝ) (regular : ContinuousOn function (Icc 0 finish)) :
      IntervalIntegrable (fun time => Real.exp (-(lambda / 2) * (finish - time)) * ‖function time‖) volume 0 finish :=
    (kernel.continuousOn.mul regular.norm).intervalIntegrable_of_Icc finishInside.1
  have convertWeighted (function : ℝ → ℝ × ℝ) (regular : ContinuousOn function (Icc 0 path.stop))
      (weighted : IntervalIntegrable (fun time => Real.exp (-lambda * time) * ‖function time‖) volume 0 finish)
      (bound : Real.exp (lambda * origin) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-lambda * time) * ‖function time‖) ≤
          tolerance / 3 * changed.seed (receiver.val + 1)) :
      (∫ time in (0 : ℝ)..finish, Real.exp (-(lambda / 2) * (finish - time)) * ‖function time‖) ≤ tolerance / 3 := by
    have firstI := ((show Continuous (fun time : ℝ => Real.exp (-(-(lambda / 2)) * time)) by fun_prop).continuousOn.mul
      (regular.mono subset).norm).intervalIntegrable_of_Icc (μ := volume) finishInside.1
    have comparison := intervalIntegral.exp_mul_integral_weighted_mono_rate finishInside.1
      (show -(lambda / 2) ≤ lambda by linarith only [lambdaPositive]) firstI weighted (fun _ _ => norm_nonneg _)
    have cancellation : Real.exp (lambda * finish) = Real.exp (lambda * (finish - origin)) * Real.exp (lambda * origin) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [cancellation, mul_assoc] at comparison
    have small := comparison.trans (mul_le_mul_of_nonneg_left bound (Real.exp_pos _).le)
    change EulerNonuniqueness.exponentialResponse (-(lambda / 2)) (fun time => ‖function time‖) finish ≤ _ at small
    rw [EulerNonuniqueness.exponentialResponse_eq_integral] at small
    exact small.trans (by nlinarith only [mul_le_mul_of_nonneg_left exposure (by positivity : 0 ≤ tolerance / 3)])
  change ContinuousOn coarser (Icc 0 path.stop) at coarseContinuous
  change IntervalIntegrable (fun time => Real.exp (-lambda * time) * ‖coarser time‖) volume 0 finish at coarseI
  change Real.exp (lambda * origin) *
    (∫ time in (0 : ℝ)..finish, Real.exp (-lambda * time) * ‖coarser time‖) ≤
      tolerance / 3 * changed.seed (receiver.val + 1) at coarseBound
  change ContinuousOn older (Icc 0 path.stop) at olderContinuous
  change IntervalIntegrable (fun time => Real.exp (-lambda * time) * ‖older time‖) volume 0 finish at olderI
  change Real.exp (lambda * origin) *
    (∫ time in (0 : ℝ)..finish, Real.exp (-lambda * time) * ‖older time‖) ≤
      tolerance / 3 * changed.seed (receiver.val + 1) at olderBound
  have coarseSmall := convertWeighted coarser coarseContinuous coarseI coarseBound
  have olderSmall := convertWeighted older olderContinuous olderI olderBound
  change (∫ time in (0 : ℝ)..finish, Real.exp (-(lambda / 2) * (finish - time)) * ‖input nearest time‖) ≤ tolerance / 3 at nearestBound
  have leadingI := (kernel.continuousOn.mul leadingOn.snd.abs).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have coarseKI := kernelI coarser (coarseContinuous.mono subset)
  have olderKI := kernelI older (olderContinuous.mono subset)
  have nearestKI := kernelI (input nearest) nearestContinuous
  have upperI := (coarseKI.add nearestKI).add olderKI
  have comparison := intervalIntegral.integral_mono_on finishInside.1 leadingI upperI (by
    intro time inside
    have actual := identity time (subset inside)
    change leading time = coarser time + input nearest time + older time at actual
    have projection : |(leading time).2| ≤ ‖leading time‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le (leading time)
    have triangle : |(leading time).2| ≤ ‖coarser time‖ + ‖input nearest time‖ + ‖older time‖ :=
      projection.trans (by rw [actual]; exact (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _))
    simpa only [mul_add] using mul_le_mul_of_nonneg_left triangle (Real.exp_pos (-(lambda / 2) * (finish - time))).le)
  rw [intervalIntegral.integral_add (coarseKI.add nearestKI) olderKI,
    intervalIntegral.integral_add coarseKI nearestKI] at comparison
  refine ⟨leadingOn, leadingI, ?_⟩
  linarith only [comparison, coarseSmall, nearestBound, olderSmall]

end EulerNonuniqueness.Paper
