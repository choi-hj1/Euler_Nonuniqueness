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

private theorem follower_weighted_convolution_continuous {forcing : ℝ → ℝ} {finish : ℝ}
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

theorem exists_uniform_actual_follower_envelope_arbitrary_weight_return :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    max 2 (2 * constant) ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant boundaryConstant : ℝ,
    threshold ≤ thresholdMax → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ drive : Fin count, drive.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ receiver : Fin count, receiver.val < drive.val → ∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time receiver| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time receiver| ≤ radius) →
    let changed : Scales := {scales with frequency := frequency}
    let envelope := prepared.coarserFollowerEnvelope drive
    let remaining := prepared.followerStrictlyFinerForcing drive
    let driver := fun time => prepared.weightedMacroSourceState time drive
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let rate := constant * changed.omega (drive.val + 1) / changed.ratio + constant * rho
    ∀ weight : ℝ, 2 * changed.omega (drive.val + 1) ≤ weight →
    ContinuousOn envelope (Icc 0 finish) ∧ ContinuousOn driver (Icc 0 finish) ∧ ContinuousOn remaining (Icc 0 finish) ∧
    envelope 0 = 0 ∧ rate ≤ changed.omega (drive.val + 1) ∧ weight / 2 ≤ weight - rate ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * envelope time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * driver time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * remaining time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * envelope time) ≤
      (2 * constant / weight) *
        (rho * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * driver time) +
          ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * remaining time) := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, factory⟩ :=
    exists_uniform_actual_follower_resolved_response
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, responses⟩ := factory factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant boundaryConstant
    thresholdBound referenceNonnegative boundaryOne orbit sectionTime
  filter_upwards [responses scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant boundaryConstant
      thresholdBound referenceNonnegative boundaryOne orbit sectionTime, eventually_ge_atTop (1 : ℝ)] with frequency response frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path drive nonterminal finish finishNonnegative finishBound small
  dsimp only
  intro weight weightLower
  let changed : Scales := {scales with frequency := frequency}
  let envelope := prepared.coarserFollowerEnvelope drive
  let remaining := prepared.followerStrictlyFinerForcing drive
  let driver := fun time => prepared.weightedMacroSourceState time drive
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let rate := constant * changed.omega (drive.val + 1) / changed.ratio + constant * rho
  let forcing := fun time => rho * driver time + remaining time
  let convolution := fun time => ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current
  let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  obtain ⟨envelopeContinuous, driverContinuous, remainingContinuous, _, _, _, initialZero, rateBound, _, history⟩ :=
    response count phase dipoleAngle prepared path drive nonterminal finish finishNonnegative finishBound small
  change rate ≤ changed.omega (drive.val + 1) at rateBound
  change 2 * changed.omega (drive.val + 1) ≤ weight at weightLower
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioOne : 1 ≤ changed.ratio := by change 1 ≤ scales.ratio; linarith only [ratioBound]
  have ratioPositive : 0 < changed.ratio := zero_lt_one.trans_le ratioOne
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (drive.val + 1)
  have weightPositive : 0 < weight := (mul_pos (by norm_num : (0 : ℝ) < 2) omegaPositive).trans_le weightLower
  have gapHalf : weight / 2 ≤ weight - rate := by
    have half : changed.omega (drive.val + 1) ≤ weight / 2 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa only [mul_comm] using weightLower)
    apply le_sub_iff_add_le.mpr
    exact (add_le_add_left (rateBound.trans half) (weight / 2)).trans_eq (by ring)
  have gapPositive : 0 < weight - rate := (half_pos weightPositive).trans_le gapHalf
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    exact add_nonneg (mul_nonneg (by norm_num) hessianNonnegative) (mul_nonneg (by norm_num) strainNonnegative)
  have driverNonnegative (time : ℝ) : 0 ≤ driver time :=
    mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time drive)
  have remainingNonnegative (time : ℝ) : 0 ≤ remaining time := norm_nonneg _
  have forcingContinuous : ContinuousOn forcing (Icc 0 finish) := (continuousOn_const.mul driverContinuous).add remainingContinuous
  have convolutionContinuous := follower_weighted_convolution_continuous finishNonnegative forcingContinuous rate
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have envelopeI := (exponentialContinuous.continuousOn.mul envelopeContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have driverI := (exponentialContinuous.continuousOn.mul driverContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have remainingI := (exponentialContinuous.continuousOn.mul remainingContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have convolutionI := (exponentialContinuous.continuousOn.mul convolutionContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have constantNonnegative : 0 ≤ constant := zero_le_one.trans constantOne
  have integrated : weighted envelope ≤ constant * weighted convolution := by
    have comparison := intervalIntegral.integral_mono_on finishNonnegative envelopeI (convolutionI.const_mul constant) (by
      intro time inside
      have scaled := mul_le_mul_of_nonneg_left (history time inside).2 (Real.exp_pos (-weight * time)).le
      convert scaled using 1; ring)
    simpa only [intervalIntegral.integral_const_mul] using comparison
  have forcingIdentity : weighted forcing = rho * weighted driver + weighted remaining := by
    dsimp only [weighted, forcing]
    simp_rw [mul_add, show ∀ time, Real.exp (-weight * time) * (rho * driver time) =
      rho * (Real.exp (-weight * time) * driver time) by intro time; ring]
    rw [intervalIntegral.integral_add (driverI.const_mul rho) remainingI, intervalIntegral.integral_const_mul]
  have convolutionBound := EulerNonuniqueness.weighted_exponential_convolution_integral_le forcingContinuous
    (sub_pos.mp gapPositive) finishNonnegative (fun time _ => add_nonneg (mul_nonneg rhoNonnegative (driverNonnegative time)) (remainingNonnegative time))
  change weighted convolution ≤ weighted forcing / (weight - rate) at convolutionBound
  rw [forcingIdentity] at convolutionBound
  have numeratorNonnegative : 0 ≤ rho * weighted driver + weighted remaining := add_nonneg
    (mul_nonneg rhoNonnegative (intervalIntegral.integral_nonneg finishNonnegative (fun time _ => mul_nonneg (Real.exp_pos _).le (driverNonnegative time))))
    (intervalIntegral.integral_nonneg finishNonnegative (fun time _ => mul_nonneg (Real.exp_pos _).le (remainingNonnegative time)))
  have inverseBound : (rho * weighted driver + weighted remaining) / (weight - rate) ≤
      2 * (rho * weighted driver + weighted remaining) / weight := by
    have actual := div_le_div_of_nonneg_left numeratorNonnegative (half_pos weightPositive) gapHalf
    simpa only [div_div_eq_mul_div, mul_comm] using actual
  refine ⟨envelopeContinuous, driverContinuous, remainingContinuous, initialZero, rateBound, gapHalf, envelopeI, driverI, remainingI, ?_⟩
  exact (integrated.trans (mul_le_mul_of_nonneg_left (convolutionBound.trans inverseBound) constantNonnegative)).trans_eq (by ring)

end EulerNonuniqueness.Paper
