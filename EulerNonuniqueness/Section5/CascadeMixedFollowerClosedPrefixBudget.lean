import EulerNonuniqueness.Section5.CascadeMixedFollowerOriginalPrefixBudget
import EulerNonuniqueness.Section5.CascadeFollowerResolvedResponse
import EulerNonuniqueness.General.WeightedResponseIntegral

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem closed_prefix_convolution_continuous {forcing : ℝ → ℝ} {finish : ℝ}
    (finishNonnegative : 0 ≤ finish) (regular : ContinuousOn forcing (Icc 0 finish)) (rate : ℝ) :
    ContinuousOn (fun time => ∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * forcing current) (Icc 0 finish) := by
  let extended := fun time => forcing (projIcc 0 finish finishNonnegative time)
  have extendedContinuous : Continuous extended :=
    (continuousOn_iff_continuous_restrict.mp regular).comp continuous_projIcc
  have agreement (time : ℝ) (inside : time ∈ Icc 0 finish) :
      EulerNonuniqueness.exponentialResponse rate extended time =
        ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current := by
    rw [EulerNonuniqueness.exponentialResponse_eq_integral]
    apply intervalIntegral.integral_congr
    intro current member
    rw [uIcc_of_le inside.1] at member
    change Real.exp (rate * (time - current)) * forcing (projIcc 0 finish finishNonnegative current) = _
    rw [projIcc_of_mem finishNonnegative ⟨member.1, member.2.trans inside.2⟩]
  have responseContinuous : Continuous (EulerNonuniqueness.exponentialResponse rate extended) :=
    continuous_iff_continuousAt.mpr fun time =>
      (EulerNonuniqueness.hasDerivAt_exponentialResponse extendedContinuous rate time).continuousAt
  exact responseContinuous.continuousOn.congr (fun time inside => (agreement time inside).symm)

private theorem closed_prefix_absorb {remaining envelope driver known coefficient : ℝ}
    (sourceBound : remaining ≤ known + envelope)
    (envelopeBound : envelope ≤ coefficient * (driver + remaining))
    (selfTerm : coefficient * remaining ≤ (1 / 2 : ℝ) * remaining) :
    remaining ≤ 2 * known + 2 * coefficient * driver := by
  nlinarith only [sourceBound, envelopeBound, selfTerm]

theorem exists_uniform_actual_mixed_follower_closed_prefix_budget :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ responseConstant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    max 2 (4 * responseConstant) ≤ scales.ratio → 0 < scales.alpha →
    ∀ extent : ℝ, 1 ≤ extent → ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude →
    ∀ threshold ≤ thresholdMax, ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant : ℝ),
    1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ drive : Fin count, drive.val + 1 < count →
    ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ path.stop →
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, drive.val < source.val →
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
    (∀ source : Fin count, drive.val < source.val → ∀ time ∈ Icc 0 (entry source),
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
    (∀ source : Fin count, drive.val < source.val → 0 ≤ magnitude source ∧
      ∀ time ∈ Icc 0 (entry source), sharpState source time ≤
        magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    ∀ finish ∈ Icc 0 terminal,
    (∀ receiver : Fin count, receiver.val < drive.val → ∀ time ∈ Icc 0 finish,
      |unstableShape motion time receiver| + |stableShape motion time receiver| ≤ radius) →
    ∀ weight : ℝ, changed.omega (drive.val + 1) ≤ weight →
    (∀ source : Fin count, drive.val < source.val → 2 * weight ≤ coefficient * changed.omega (source.val + 1)) →
    let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
    let omega := changed.omega (drive.val + 1)
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let rate := responseConstant * omega / changed.ratio + responseConstant * rho
    let driver := fun time => prepared.weightedMacroSourceState time drive
    ContinuousOn (prepared.followerStrictlyFinerForcing drive) (Icc 0 path.stop) ∧
    ContinuousOn (prepared.coarserFollowerEnvelope drive) (Icc 0 path.stop) ∧
    ContinuousOn driver (Icc 0 finish) ∧ prepared.coarserFollowerEnvelope drive 0 = 0 ∧
    rate ≤ omega / 2 ∧ weight / 2 ≤ weight - rate ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * driver time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.followerStrictlyFinerForcing drive time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.coarserFollowerEnvelope drive time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.followerStrictlyFinerForcing drive time) ≤
      2 * (incomingConstant * extent ^ 2 * (∑ source ∈ finer,
        changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
          (1 + (changed.location (source.val + 1))⁻¹) * magnitude source /
          (coefficient * changed.omega (source.val + 1)) * Real.exp (-weight * entry source)) +
      outgoingConstant * (∑ source ∈ finer.filter (fun source => entry source < finish),
        changed.circulation (source.val + 1) *
          (changed.circulation (source.val + 1) / weight ^ 2 +
            ((1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
              ‖centroidAsymmetry motion (entry source) source‖) / weight) * Real.exp (-weight * entry source))) +
      (4 * responseConstant / weight) * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * driver time := by
  obtain ⟨sourceThreshold, sourceThresholdPositive, sourceThresholdEighth, sourceCap, sourceCapPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, sourceFactory⟩ :=
    exists_uniform_actual_mixed_follower_original_prefix_budget
  obtain ⟨responseThreshold, responseThresholdPositive, _, responseCap, responseCapPositive, responseFactory⟩ :=
    exists_uniform_actual_follower_resolved_response
  let thresholdMax := min sourceThreshold responseThreshold
  let rawCap := min sourceCap responseCap
  have capPositive : 0 < rawCap := lt_min sourceCapPositive responseCapPositive
  have sourceCapBound : rawCap ≤ sourceCap := min_le_left _ _
  have responseCapBound : rawCap ≤ responseCap := min_le_right _ _
  refine ⟨thresholdMax, lt_min sourceThresholdPositive responseThresholdPositive,
    (min_le_left _ _).trans sourceThresholdEighth, rawCap, capPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, responses⟩ :=
    responseFactory factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive extent extentOne referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant boundaryOne
  have constantNonnegative : 0 ≤ constant := zero_le_one.trans constantOne
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have responseRatio : max 2 (2 * constant) ≤ scales.ratio := by
    apply max_le ratioBound
    have large := (le_max_right (2 : ℝ) (4 * constant)).trans ratioLarge
    linarith only [large, constantOne]
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have rhoDecay := ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
    ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576)
  have feedbackDecay := rhoDecay.const_mul constant
  simp only [mul_zero, zero_add] at feedbackDecay
  filter_upwards [sourceFactory extent extentOne 1 (by norm_num) scales amplitudePositive ratioBound alphaPositive
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans (min_le_left _ _))
      orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    responses scales scaleRoot rootLarge amplitudeIdentity responseRatio alphaPositive threshold referenceConstant
      boundaryConstant (thresholdBound.trans (min_le_right _ _)) referenceNonnegative boundaryOne orbit sectionTime,
    feedbackDecay.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    eventually_ge_atTop (max (1 : ℝ) (4 * constant))]
    with frequency sources response feedbackSmall frequencyLarge
  intro count phase dipoleAngle shapeRadius monitor prepared path drive nonterminal terminal terminalNonnegative terminalBound
    entry initialDistance direction
  dsimp only
  intro entries extents coefficient coefficientPositive magnitude profiles finish finishInside small weight omegaWeight rateBounds
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (drive.val + 1)
  let envelope := prepared.coarserFollowerEnvelope drive
  let driver := fun time => prepared.weightedMacroSourceState time drive
  let remaining := prepared.followerStrictlyFinerForcing drive
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let rate := constant * omega / changed.ratio + constant * rho
  let forcing := fun time => rho * driver time + remaining time
  let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
  let known := incomingConstant * extent ^ 2 * (∑ source ∈ finer,
      changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
        (1 + (changed.location (source.val + 1))⁻¹) * magnitude source /
        (coefficient * changed.omega (source.val + 1)) * Real.exp (-weight * entry source)) +
    outgoingConstant * (∑ source ∈ finer.filter (fun source => entry source < finish),
      changed.circulation (source.val + 1) * (changed.circulation (source.val + 1) / weight ^ 2 +
        ((1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
          ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion (entry source) source‖) / weight) *
        Real.exp (-weight * entry source))
  have frequencyOne : 1 ≤ frequency := (le_max_left _ _).trans frequencyLarge
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioOne : 1 ≤ changed.ratio := by change 1 ≤ scales.ratio; linarith only [ratioBound]
  have ratioPositive : 0 < changed.ratio := zero_lt_one.trans_le ratioOne
  have omegaLarge : frequency ≤ omega := changed.omega_ge_frequency frequencyPositive ratioOne _
  have omegaOne : 1 ≤ omega := frequencyOne.trans omegaLarge
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have weightPositive : 0 < weight := omegaPositive.trans_le omegaWeight
  have macroInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have driverInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).weightedMacroSourceState = prepared.weightedMacroSourceState := by
    funext time source
    simp only [CascadeSourcePreparedPair.weightedMacroSourceState, macroInvariant]
  have envelopeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).coarserFollowerEnvelope = prepared.coarserFollowerEnvelope := by
    funext index time
    simp only [CascadeSourcePreparedPair.coarserFollowerEnvelope, driverInvariant]
  have remainingInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).followerStrictlyFinerForcing = prepared.followerStrictlyFinerForcing := rfl
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have sourceData := sources count phase dipoleAngle (prepared.enlargeCap sourceCapBound) path drive terminal terminalNonnegative
    terminalBound entry initialDistance direction entries extents coefficient coefficientPositive magnitude
    (by simpa only [rawInvariant] using profiles)
    finish finishInside weight weightPositive rateBounds
  simp only [remainingInvariant, envelopeInvariant, rawInvariant, one_mul] at sourceData
  dsimp only [CascadeSourcePreparedPair.enlargeCap] at sourceData
  obtain ⟨remainingContinuous, envelopeContinuous, remainingI, envelopeI, sourceBound⟩ := sourceData
  have responseData := response count phase dipoleAngle (prepared.enlargeCap responseCapBound) path drive nonterminal
    finish finishInside.1 (finishInside.2.trans terminalBound) small
  dsimp only at responseData
  simp only [envelopeInvariant, driverInvariant, remainingInvariant] at responseData
  obtain ⟨envelopeRegular, driverRegular, remainingRegular, _, _, _, initialZero, _, _, history⟩ := responseData
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho]
    positivity
  have rhoOne : rho ≤ 1 := by
    have lower := le_mul_of_one_le_left rhoNonnegative constantOne
    have upper : constant * rho ≤ 1 / 4 := feedbackSmall.le
    exact lower.trans (upper.trans (by norm_num))
  have coarseRate : constant * omega / changed.ratio ≤ omega / 4 := by
    apply (div_le_iff₀ ratioPositive).mpr
    have large := mul_le_mul_of_nonneg_right ((le_max_right (2 : ℝ) (4 * constant)).trans ratioLarge) omegaPositive.le
    nlinarith only [large]
  have rateHalf : rate ≤ omega / 2 := by
    have feedback : constant * rho ≤ 1 / 4 := feedbackSmall.le
    dsimp only [rate]
    linarith only [coarseRate, feedback, omegaOne]
  have gapHalf : weight / 2 ≤ weight - rate := by linarith only [rateHalf, omegaWeight]
  have gapPositive : 0 < weight - rate := (half_pos weightPositive).trans_le gapHalf
  have driverNonnegative (time : ℝ) : 0 ≤ driver time :=
    mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time drive)
  have remainingNonnegative (time : ℝ) : 0 ≤ remaining time := norm_nonneg _
  have forcingRegular : ContinuousOn forcing (Icc 0 finish) :=
    (continuousOn_const.mul driverRegular).add remainingRegular
  let convolution := fun time => ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current
  have convolutionRegular := closed_prefix_convolution_continuous finishInside.1 forcingRegular rate
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have driverI := (exponentialContinuous.continuousOn.mul driverRegular).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have convolutionI := (exponentialContinuous.continuousOn.mul convolutionRegular).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  have integrated : weighted envelope ≤ constant * weighted convolution := by
    have comparison := intervalIntegral.integral_mono_on finishInside.1 envelopeI (convolutionI.const_mul constant) (by
      intro time inside
      have scaled := mul_le_mul_of_nonneg_left (history time inside).2 (Real.exp_pos (-weight * time)).le
      (convert scaled using 1; ring))
    simpa only [intervalIntegral.integral_const_mul] using comparison
  have forcingIdentity : weighted forcing = rho * weighted driver + weighted remaining := by
    dsimp only [weighted, forcing]
    simp_rw [mul_add, show ∀ time, Real.exp (-weight * time) * (rho * driver time) =
      rho * (Real.exp (-weight * time) * driver time) by intro time; ring]
    rw [intervalIntegral.integral_add (driverI.const_mul rho) remainingI, intervalIntegral.integral_const_mul]
  have convolutionBound := EulerNonuniqueness.weighted_exponential_convolution_integral_le forcingRegular
    (sub_pos.mp gapPositive) finishInside.1 (fun time _ => add_nonneg
      (mul_nonneg rhoNonnegative (driverNonnegative time)) (remainingNonnegative time))
  change weighted convolution ≤ weighted forcing / (weight - rate) at convolutionBound
  rw [forcingIdentity] at convolutionBound
  have driverActionNonnegative : 0 ≤ weighted driver := intervalIntegral.integral_nonneg finishInside.1
    (fun time _ => mul_nonneg (Real.exp_pos _).le (driverNonnegative time))
  have remainingActionNonnegative : 0 ≤ weighted remaining := intervalIntegral.integral_nonneg finishInside.1
    (fun time _ => mul_nonneg (Real.exp_pos _).le (remainingNonnegative time))
  have numeratorBound : rho * weighted driver + weighted remaining ≤ weighted driver + weighted remaining :=
    add_le_add_right (mul_le_of_le_one_left driverActionNonnegative rhoOne) _
  have inverseBound : (weighted driver + weighted remaining) / (weight - rate) ≤
      2 * (weighted driver + weighted remaining) / weight := by
    have first := div_le_div_of_nonneg_left (add_nonneg driverActionNonnegative remainingActionNonnegative)
      (half_pos weightPositive) gapHalf
    simpa only [div_div_eq_mul_div, mul_comm] using first
  have envelopeBound : weighted envelope ≤ (2 * constant / weight) * (weighted driver + weighted remaining) := by
    have convolved := integrated.trans (mul_le_mul_of_nonneg_left convolutionBound constantNonnegative)
    have numerator := div_le_div_of_nonneg_right numeratorBound gapPositive.le
    exact convolved.trans ((mul_le_mul_of_nonneg_left (numerator.trans inverseBound) constantNonnegative).trans_eq (by ring))
  have coefficientHalf : 2 * constant / weight ≤ 1 / 2 := by
    apply (div_le_iff₀ weightPositive).mpr
    have frequencyBound : 4 * constant ≤ frequency := (le_max_right _ _).trans frequencyLarge
    linarith only [frequencyBound, omegaLarge, omegaWeight]
  have selfTerm := mul_le_mul_of_nonneg_right coefficientHalf remainingActionNonnegative
  change weighted remaining ≤ known + weighted envelope at sourceBound
  refine ⟨remainingContinuous, envelopeContinuous, driverRegular, initialZero, rateHalf, gapHalf, driverI,
    remainingI, envelopeI, ?_⟩
  change weighted remaining ≤ 2 * known + (4 * constant / weight) * weighted driver
  have scalar := closed_prefix_absorb sourceBound envelopeBound selfTerm
  have coefficientIdentity : 2 * (2 * constant / weight) = 4 * constant / weight := by ring
  simpa only [coefficientIdentity] using scalar

end EulerNonuniqueness.Paper

