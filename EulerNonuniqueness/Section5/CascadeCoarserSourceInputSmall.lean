import EulerNonuniqueness.Section5.CascadeCoarserLeadingClosedWeightedReturn
import EulerNonuniqueness.Section5.CascadeCalibratedKnownSourceBudgetFromDomains
import EulerNonuniqueness.Section5.CascadeMixedCommonSharpBudgetComparison
import EulerNonuniqueness.Section5.CascadeMacroStateCenteredBound
import EulerNonuniqueness.General.WeightedExponentialProfileBootstrap

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_coarser_source_input_small :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ rootMin ≥ (8 : ℝ),
    ∀ currentMagnitude : ℝ, 0 ≤ currentMagnitude → ∀ tolerance : ℝ, 0 < tolerance →
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
    let coarseInput := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
      relativeBlockSourceShapeInput changed motion prepared.reference receiver source time
    ContinuousOn coarseInput (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-lambda * time) • coarseInput time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-lambda * time) * ‖coarseInput time‖) volume 0 finish ∧
    Real.exp (lambda * origin) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-lambda * time) * ‖coarseInput time‖) ≤
        tolerance * changed.seed (receiver.val + 1) := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive,
    coarseConstant, coarseNonnegative, incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, factories⟩ :=
    exists_uniform_actual_coarser_leading_closed_weighted_return
  have calibrated := exists_uniform_calibrated_timed_known_source_budget_of_domains
    incomingNonnegative outgoingNonnegative incomingNonnegative outgoingNonnegative (le_refl (0 : ℝ))
  dsimp only at calibrated
  simp only [mul_zero, zero_mul, add_zero] at calibrated
  obtain ⟨knownOne, calibrations⟩ := calibrated
  let knownMagnitude := 1 + 8 * (4 * outgoingConstant + 1)
  have knownNonnegative : 0 ≤ knownMagnitude := zero_le_one.trans knownOne
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, responseE, responseEOne, responseK, responseKOne, rootMin, rootEight, parameters⟩ :=
    factories factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, rootMin, rootEight, ?_⟩
  intro currentMagnitude currentNonnegative tolerance tolerancePositive extent magnitudeMax distanceMax sourceRate
    extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  let accuracy := tolerance / (8 * (1 + currentMagnitude))
  have accuracyPositive : 0 < accuracy := by dsimp only [accuracy]; positivity
  obtain ⟨knownRatio, knownTwo, knownFactory⟩ := calibrations extent magnitudeMax distanceMax sourceRate
    extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  let responseRatio := max 2 (max (2 * responseE) (4 * responseK))
  let ratioMin := max responseRatio knownRatio
  refine ⟨ratioMin, (le_max_left _ _).trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant referenceNonnegative
    referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError boundaryOne timingNonnegative ratioSeparation
  have responseRatioBound : responseRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have knownRatioBound : knownRatio ≤ scales.ratio := (le_max_right _ _).trans ratioLarge
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans responseRatioBound
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have growthOne : 1 ≤ 2 * Real.sqrt 2 := by
    have root : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    linarith only [root]
  let rhoAt := fun frequency : ℝ => 216360000 * ({scales with frequency := frequency} : Scales).hessian +
    576 * ({scales with frequency := frequency} : Scales).strain
  have rhoDecay : Tendsto rhoAt atTop (𝓝 0) := by
    simpa only [rhoAt, mul_zero, zero_add] using
      (((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
        ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576))
  have returnDecay := rhoDecay.const_mul (coarseConstant * responseE * knownMagnitude)
  simp only [mul_zero] at returnDecay
  filter_upwards [parameters extent extentOne accuracy accuracyPositive scales scaleRoot rootLarge amplitudeIdentity
      responseRatioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
      orbit sectionTime boundaryConstant boundaryOne,
    knownFactory scales amplitudePositive knownRatioBound alphaPositive alphaSmall ratioPower (2 * Real.sqrt 2) timingError
      growthOne timingNonnegative ratioSeparation sectionTime scaleRoot boundaryConstant (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    returnDecay.eventually (eventually_lt_nhds tolerancePositive), eventually_ge_atTop (1 : ℝ)] with
      frequency estimate knownEstimate lengths returnSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal entry initialDistance direction
  dsimp only
  intro entries extents magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
    finish finishInside small rateBounds currentProfile
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (receiver.val + 1)
  let lambda := 2 * Real.sqrt 2 * omega
  let location := changed.location (receiver.val + 1)
  let seed := changed.seed (receiver.val + 1)
  let origin := entry ⟨receiver.val + 1, nonterminal⟩
  let rho := rhoAt frequency
  let macroValue := fun time => prepared.macroSourceState time receiver
  let coarseInput := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
    relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion prepared.reference receiver source time
  let commonBudget := prepared.mixedFollowerSourcePrefixBudget receiver incomingConstant outgoingConstant extent sourceRate
    entry initialDistance magnitude lambda finish
  let sharpBudget := prepared.mixedSelectedFinerSourcePrefixBudget receiver incomingConstant outgoingConstant extent sourceRate
    entry initialDistance magnitude lambda finish
  let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-lambda * time) * function time
  let scale := seed * Real.exp (-lambda * origin)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have lambdaPositive : 0 < lambda := by dsimp only [lambda]; positivity
  have lambdaOmega : omega ≤ lambda := by
    exact (le_mul_of_one_le_left omegaPositive.le growthOne)
  have lambdaDouble : 2 * omega ≤ lambda := by
    have root : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    dsimp only [lambda]
    nlinarith only [mul_le_mul_of_nonneg_right root omegaPositive.le]
  have locationPositive : 0 < location := changed.location_pos _
  have scaleNonnegative : 0 ≤ scale := mul_nonneg (changed.seed_pos frequencyPositive ratioPositive _).le (Real.exp_pos _).le
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho, rhoAt]; positivity
  have distanceNonnegative' (source : Fin count) (below : receiver.val < source.val) : 0 ≤ initialDistance source :=
    (by norm_num : (0 : ℝ) ≤ 512).trans (entries source below).2.2.1
  have data := estimate count phase dipoleAngle prepared path receiver nonterminal entry initialDistance direction entries extents
    sourceRate sourceRatePositive magnitude profiles finish finishInside small lambda lambdaDouble rateBounds
  dsimp only at data
  obtain ⟨coarseContinuous, macroContinuous, vectorI, normI, macroI, coarseBound⟩ := data
  change weighted (fun time => ‖coarseInput time‖) ≤ accuracy * weighted macroValue +
    (4 * coarseConstant * responseE * rho / (lambda * location ^ 4)) * commonBudget at coarseBound
  have known := knownEstimate count (thresholdBound.trans thresholdEighth |>.trans (by norm_num))
    (factorSmall.trans (by norm_num)) prepared path receiver nonterminal entry initialDistance magnitude actualTime timeIdentity
    (fun source below => ⟨(entries source below).1, (entries source below).2.1⟩) nearestTiming sourceTiming timeOrder
    (fun source below => ⟨(profiles source below).1, magnitudeUpper source below⟩)
    (fun source below => ⟨distanceNonnegative' source below, distanceUpper source below⟩) domains finish
  simp only [zero_div, zero_mul, add_zero] at known
  change Real.exp (lambda * origin) * (8 * sharpBudget) ≤ knownMagnitude * seed ∧
    8 * sharpBudget ≤ knownMagnitude * seed * Real.exp (-lambda * origin) at known
  have knownSharp : 8 * sharpBudget ≤ knownMagnitude * scale := by
    simpa only [scale, mul_assoc] using known.2
  have commonComparison := prepared.mixed_common_sharp_budget_comparison receiver
    (incomingConstant := incomingConstant) (outgoingConstant := outgoingConstant) (extent := extent)
    (coefficient := sourceRate) (weight := lambda) (finish := finish) (rho := rho) entry initialDistance magnitude
    frequencyPositive ratioBound incomingNonnegative outgoingNonnegative sourceRatePositive lambdaPositive rhoNonnegative
    (fun source below => (profiles source below).1) distanceNonnegative'
  change rho / (omega * location ^ 4) * commonBudget ≤ (rho / changed.frequency) * sharpBudget at commonComparison
  have commonNonnegative : 0 ≤ commonBudget := by
    dsimp only [commonBudget, CascadeSourcePreparedPair.mixedFollowerSourcePrefixBudget]
    apply add_nonneg
    · apply mul_nonneg (mul_nonneg incomingNonnegative (sq_nonneg extent))
      apply Finset.sum_nonneg
      intro source member
      have below := (Finset.mem_filter.mp member).2
      have magnitudeNonnegative' := (profiles source below).1
      have gamma := (changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le
      have sourceLocation := (changed.location_pos (source.val + 1)).le
      have sourceOmega := (changed.omega_pos frequencyPositive ratioPositive (source.val + 1)).le
      positivity
    · apply mul_nonneg outgoingNonnegative
      apply Finset.sum_nonneg
      intro source member
      have below := (Finset.mem_filter.mp (Finset.mem_filter.mp member).1).2
      have distanceNonnegative'' := distanceNonnegative' source below
      have gamma := (changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le
      positivity
  have macroProfile (time : ℝ) (inside : time ∈ Icc 0 finish) :
      macroValue time ≤ 4 * currentMagnitude * seed * Real.exp (lambda * (time - origin)) := by
    have actual := prepared.macroSourceState_le_centered_and_raw path ⟨inside.1, inside.2.trans finishInside.2⟩ receiver
    rw [← prepared.referenceIdentity, norm_sub_rev] at actual
    have lengthRatio : changed.length (receiver.val + 1) / changed.location (receiver.val + 1) ≤ 1 :=
      (div_le_one (changed.location_pos _)).mpr (by simpa only [one_mul] using (lengths (receiver.val + 1)).le)
    have centeredNonnegative : 0 ≤ prepared.rawSourceCenteredState time receiver :=
      div_nonneg (norm_nonneg _) (changed.length_pos _).le
    have rawNonnegative : 0 ≤ ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch := by
      apply Finset.sum_nonneg
      intro patch _
      dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    have centerNonnegative := div_nonneg
      (norm_nonneg (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time receiver -
        quadrupoleCenter prepared.reference time receiver)) (changed.location_pos (receiver.val + 1)).le
    have momentNonnegative := norm_nonneg (relativeNormalizedFirstMoment changed prepared.trajectory.movingFamily.patchMotion
      prepared.reference receiver time)
    have centeredScaled := mul_le_mul_of_nonneg_right lengthRatio
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) centeredNonnegative)
    have sharp := currentProfile time inside
    change macroValue time ≤ _ at actual
    nlinarith only [actual, centeredScaled, sharp, rawNonnegative, centerNonnegative, momentNonnegative]
  have macroAction := intervalIntegral.integral_exp_neg_mul_le_of_same_rate_majorant finishInside.1 macroI macroProfile
  have macroReduced : weighted macroValue ≤ 4 * currentMagnitude * scale := by
    apply macroAction.trans
    have finishOne : finish ≤ 1 := finishInside.2.trans path.stopBound
    convert mul_le_mul_of_nonneg_right finishOne (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) currentNonnegative) scaleNonnegative) using 1 <;> dsimp only [scale] <;> ring
  have currentSmall : accuracy * weighted macroValue ≤ (tolerance / 2) * scale := by
    have scaled := mul_le_mul_of_nonneg_left macroReduced accuracyPositive.le
    have coefficient : accuracy * (4 * currentMagnitude) ≤ tolerance / 2 := by
      rw [show accuracy * (4 * currentMagnitude) =
        (tolerance * (4 * currentMagnitude)) / (8 * (1 + currentMagnitude)) by dsimp only [accuracy]; ring]
      apply (div_le_iff₀ (by positivity : 0 < 8 * (1 + currentMagnitude))).mpr
      nlinarith only [tolerancePositive, currentNonnegative]
    exact scaled.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right coefficient scaleNonnegative)
  have returned : (4 * coarseConstant * responseE * rho / (lambda * location ^ 4)) * commonBudget ≤
      (tolerance / 2) * scale := by
    have denominatorBound : rho / (lambda * location ^ 4) ≤ rho / (omega * location ^ 4) :=
      div_le_div_of_nonneg_left rhoNonnegative (mul_pos omegaPositive (pow_pos locationPositive 4))
        (mul_le_mul_of_nonneg_right lambdaOmega (pow_nonneg locationPositive.le 4))
    have comparison := (mul_le_mul_of_nonneg_right denominatorBound commonNonnegative).trans commonComparison
    have scaled := mul_le_mul_of_nonneg_left comparison (show 0 ≤ 4 * coarseConstant * responseE by positivity)
    have sharpScaled := mul_le_mul_of_nonneg_left knownSharp
      (show 0 ≤ coarseConstant * responseE * rho / (2 * changed.frequency) by positivity)
    have coefficientBound : coarseConstant * responseE * rho / (2 * changed.frequency) * knownMagnitude ≤ tolerance / 2 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 2 * changed.frequency)).mpr
      have actual : coarseConstant * responseE * knownMagnitude * rho < tolerance := returnSmall
      have frequencyOne' : 1 ≤ changed.frequency := frequencyOne
      have frequencyScaled := mul_le_mul_of_nonneg_left frequencyOne' tolerancePositive.le
      calc
        coarseConstant * responseE * rho * knownMagnitude = coarseConstant * responseE * knownMagnitude * rho := by ring
        _ ≤ tolerance := actual.le
        _ ≤ tolerance * changed.frequency := by simpa only [mul_one] using frequencyScaled
        _ = tolerance / 2 * (2 * changed.frequency) := by ring
    have finalBound := mul_le_mul_of_nonneg_right coefficientBound scaleNonnegative
    have combine := scaled.trans (by
      convert sharpScaled using 1
      field_simp
      ring)
    convert combine.trans (by simpa only [mul_assoc] using finalBound) using 1
    ring
  have unnormalized : weighted (fun time => ‖coarseInput time‖) ≤ tolerance * scale := by
    linarith only [coarseBound, currentSmall, returned]
  refine ⟨coarseContinuous, vectorI, normI, ?_⟩
  have normalized := mul_le_mul_of_nonneg_left unnormalized (Real.exp_pos (lambda * origin)).le
  convert normalized using 1
  dsimp only [scale]
  rw [show Real.exp (lambda * origin) * (tolerance * (seed * Real.exp (-lambda * origin))) =
    tolerance * seed * (Real.exp (lambda * origin) * Real.exp (-lambda * origin)) by ring,
    ← Real.exp_add, show lambda * origin + -lambda * origin = 0 by ring, Real.exp_zero, mul_one]

end EulerNonuniqueness.Paper
